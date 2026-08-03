/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.frontend.transformation.grammar.function;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.grammar.UtilsKt.textWithWS;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.anytype.Dereference;
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.ExpressionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseChecker;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.GlobalDeclUsageVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.*;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.*;
import java.util.stream.Stream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

/**
 * FunctionVisitor is responsible for the instantiation of high-level model elements, such as
 * Programs, Functions, and Statements. It employs a TypeVisitor instance to provide type
 * information, a DeclarationVisitor instance to provide information on declarations (both global
 * and local, complete with initializations) and an ExpressionVisitor instance to provide
 * information on Expressions in the source code.
 */
public class FunctionVisitor extends IncludeHandlingCBaseVisitor<CStatement> {
    private final ParseContext parseContext;
    private final DeclarationVisitor declarationVisitor;
    private final GlobalDeclUsageVisitor globalDeclUsageVisitor;
    private final TypeVisitor typeVisitor;
    private final TypedefVisitor typedefVisitor;
    private final Logger uniqueWarningLogger;

    private final LinkedList<Tuple2<ParserRuleContext, Optional<CCompound>>>
            currentStatementContext = new LinkedList<>();

    public void clear() {
        variables.clear();
        atomicVariables.clear();
        flatVariables.clear();
        functions.clear();
        currentStatementContext.clear();
    }

    private final Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables;
    private final Set<VarDecl<?>> atomicVariables;
    private int anonCnt = 0;
    private final List<VarDecl<?>> flatVariables;
    private final Map<VarDecl<?>, CDeclaration> functions;

    private void createVars(CDeclaration declaration) {
        String name = declaration.getName();
        createVars(name, declaration, designatorType(declaration));
    }

    /**
     * The type of the variable that stands for a declaration where its name is *used*.
     *
     * <p>For an ordinary declaration that is simply its type. For a *function* it is not: the value
     * of a function designator is the function's address, and the variable has to be able to hold
     * one -- `FunctionIds` numbers them from `0x10000000`, so it needs 29 bits. Typing it by the
     * function's return type instead made `void f(int)` a **one-bit** variable, which silently
     * truncated the id to 0; the dispatch guard `fp == id(f)` then could not hold, the branch was
     * infeasible, and the callee was never explored -- reporting a program *safe* on the strength
     * of a call it had quietly dropped. Anything narrower than 29 bits did it: `char`, `short`,
     * `_Bool`, `void`.
     */
    private CComplexType designatorType(CDeclaration declaration) {
        CComplexType actualType = declaration.getActualType();
        return declaration.isFunc() ? new CPointer(null, actualType, parseContext) : actualType;
    }

    /**
     * A fresh unnamed local, registered like any other variable so that it reaches the XCFA. Used
     * where a value has to be captured before a later statement can invalidate it.
     */
    public VarDecl<?> createTempVar(CComplexType type, String hint) {
        VarDecl<?> varDecl = Var("__theta_" + hint + anonCnt++, type.getSmtType());
        flatVariables.add(varDecl);
        parseContext.getMetadata().create(varDecl.getRef(), "cType", type);
        return varDecl;
    }

    private String getName(final String name) {
        final StringJoiner sj = new StringJoiner("::");
        for (Iterator<Tuple2<String, Map<String, VarDecl<?>>>> iterator =
                        variables.descendingIterator();
                iterator.hasNext(); ) {
            Tuple2<String, Map<String, VarDecl<?>>> variable = iterator.next();
            if (!variable.get1().equals("")) sj.add(variable.get1());
        }
        sj.add(name);
        return sj.toString();
    }

    private void createVars(String name, CDeclaration declaration, CComplexType type) {
        Tuple2<String, Map<String, VarDecl<?>>> peek = variables.peek();
        VarDecl<?> varDecl = Var(getName(name), type.getSmtType());
        if (peek.get2().containsKey(name)) {
            uniqueWarningLogger.write(
                    Level.INFO, "WARNING: Variable already exists: " + name + "\n");
            varDecl = peek.get2().get(name);
        }
        peek.get2().put(name, varDecl);
        flatVariables.add(varDecl);
        // The variable is atomic when its own type is -- `int * _Atomic p`, not `_Atomic int *p`,
        // where it is what p points at that is atomic and p itself an ordinary variable.
        if (type.isAtomic()) {
            atomicVariables.add(varDecl);
        }
        parseContext.getMetadata().create(varDecl.getRef(), "cType", type);
        parseContext.getMetadata().create(varDecl.getName(), "cName", name);
        if (declaration.isFuncPointer()) {
            // Marks the variable as holding a function id, so that a call through it is dispatched
            // over the candidate set instead of being treated as a data pointer.
            parseContext.getMetadata().create(varDecl.getRef(), "isFunctionPointer", true);
        }
        declaration.addVarDecl(varDecl);
    }

    public FunctionVisitor(final ParseContext parseContext, Logger uniqueWarningLogger) {
        this.declarationVisitor = new DeclarationVisitor(parseContext, this, uniqueWarningLogger);
        this.uniqueWarningLogger = uniqueWarningLogger;
        this.typedefVisitor = declarationVisitor.getTypedefVisitor();
        this.typeVisitor = declarationVisitor.getTypeVisitor();
        variables = new ArrayDeque<>();
        variables.push(Tuple2.of("", new LinkedHashMap<>()));
        flatVariables = new ArrayList<>();
        functions = new LinkedHashMap<>();
        this.parseContext = parseContext;
        globalDeclUsageVisitor = new GlobalDeclUsageVisitor(declarationVisitor);
        atomicVariables = new LinkedHashSet<>();
        // Lets `typeof(x)` resolve x against the scope we are currently in. Lazy, because the scope
        // stack is pushed and popped as bodies are visited. Null function visitor on purpose -- see
        // TypeVisitor#scopedExpressionVisitor.
        this.typeVisitor.setScopedExpressionVisitor(
                () ->
                        new ExpressionVisitor(
                                atomicVariables,
                                parseContext,
                                null,
                                variables,
                                functions,
                                typedefVisitor,
                                typeVisitor,
                                uniqueWarningLogger));
    }

    /**
     * `malloc` returns a pointer. Recording that up front, rather than relying on the program's own
     * declaration, keeps its call type right in the two cases where no usable declaration reaches
     * us:
     *
     * <ul>
     *   <li>a fixed-size array declaration, which is lowered to a synthetic `malloc` call even
     *       though the program never mentions `malloc`;
     *   <li>the common glibc spelling `void *malloc(size_t);` -- an unnamed typedef'd parameter --
     *       which the parser cannot tell from a declaration of a *variable* named `malloc` (an
     *       identifier is also a candidate type name), and so never records a return type for.
     * </ul>
     *
     * <p>Without it the call is typed `int`, which silently coincides with a pointer under ILP32
     * and blows up under LP64. A real declaration parsed later simply overwrites this with the same
     * (pointer) type.
     */
    private void declareMallocReturnsPointer() {
        parseContext
                .getMetadata()
                .create(
                        "malloc",
                        "cType",
                        new CPointer(null, CComplexType.getSignedInt(parseContext), parseContext));
    }

    @Override
    public CStatement visitCompilationUnit(CParser.CompilationUnitContext ctx) {
        variables.clear();
        atomicVariables.clear();
        variables.push(Tuple2.of("", new LinkedHashMap<>()));
        flatVariables.clear();
        functions.clear();
        declareMallocReturnsPointer();

        // ExpressionVisitor.setBitwise(ctx.accept(BitwiseChecker.instance));
        ctx.accept(typedefVisitor);

        List<CParser.ExternalDeclarationContext> globalUsages =
                globalDeclUsageVisitor.getGlobalUsages(ctx);

        // if arithemetic is set on efficient, we change it to either bv or int arithmetic here
        if (parseContext.getArithmetic()
                == ArithmeticType
                        .efficient) { // if it wasn't on efficient, the check returns manual
            Set<ArithmeticTrait> arithmeticTraits =
                    BitwiseChecker.gatherArithmeticTraits(parseContext, globalUsages);
            parseContext.setArithmetic(
                    arithmeticTraits.contains(ArithmeticTrait.BITWISE)
                                    || arithmeticTraits.contains(ArithmeticTrait.FLOAT)
                            ? ArithmeticType.bitvector
                            : ArithmeticType.integer);
        }

        Set<CDeclaration> typedefs = ctx.accept(typedefVisitor);
        for (CDeclaration typedef : typedefs) {
            parseContext
                    .getMetadata()
                    .create(typedef.getName(), "cTypedefName", typedef.getActualType());
        }

        // Introduce every function's name before any global declaration is processed. A function has
        // file scope, so C guarantees it is visible wherever the source refers to it -- but the
        // order these contexts are visited in is not the source order: a global that is declared
        // early and *defined* later (`int (*p)(void);` ... `int (*p)(void) = f;`) keeps its original
        // position while adopting the later context (see GlobalDeclUsageVisitor), so its initializer
        // is evaluated here long before the `f` it names would be reached. That made whole driver
        // families die with "No such variable or macro: <function>". Creating the names up front
        // costs nothing: these functions are visited below anyway, and each adopts the variable made
        // here rather than making its own (the prototype-before-definition path).
        for (CParser.ExternalDeclarationContext externalDeclarationContext : globalUsages) {
            if (externalDeclarationContext
                    instanceof CParser.ExternalFunctionDefinitionContext funcDefCtx) {
                CParser.FunctionDefinitionContext funcDef = funcDefCtx.functionDefinition();
                CSimpleType returnType = funcDef.declarationSpecifiers().accept(typeVisitor);
                if (returnType.isTypedef()) continue;
                CDeclaration funcDecl = funcDef.declarator().accept(declarationVisitor);
                funcDecl.setType(returnType);
                if (funcDecl.getName() != null
                        && !variables.peek().get2().containsKey(funcDecl.getName())) {
                    parseContext
                            .getMetadata()
                            .create(funcDecl.getName(), "cType", returnType.getActualType());
                    createVars(funcDecl);
                    // Record it as a function too, not just as a name. Taking a function's address
                    // is recognised by looking the variable up in this map
                    // (registerIfFunctionUsedAsValue), and the id that lookup registers is what
                    // initialises the address. Creating the variable here without the entry made
                    // the later prototype/definition skip its own registration -- the name resolved,
                    // but every address-taken function lost its id and its initial value.
                    for (VarDecl<?> varDecl : funcDecl.getVarDecls()) {
                        functions.put(varDecl, funcDecl);
                    }
                }
            }
        }

        CProgram program = new CProgram(parseContext);
        for (CParser.ExternalDeclarationContext externalDeclarationContext : globalUsages) {
            CStatement accept = externalDeclarationContext.accept(this);
            if (accept instanceof CFunction) {
                program.getFunctions().add((CFunction) accept);
            } else if (accept instanceof CDecls) {
                program.getGlobalDeclarations().addAll(((CDecls) accept).getcDeclarations());
            }
        }
        recordMetadata(ctx, program);
        return program;
    }

    public void recordMetadataCommon(ParserRuleContext ctx, CStatement statement) {
        Token start = ctx.getStart();
        Token stop = ctx.getStop();
        String stopText = stop.getText();
        String[] stopTextLines = stopText.split("\r\n|\r|\n", -1);
        int stopLines = stopTextLines.length - 1;
        int lineNumberStart = start.getLine();
        int colNumberStart = start.getCharPositionInLine();
        int lineNumberStop = stop.getLine() + stopLines;
        int colNumberStop =
                stopLines == 0
                        ? stop.getCharPositionInLine() + stopText.length() - 1
                        : stopTextLines[stopLines].length();
        int offsetStart = start.getStartIndex();
        int offsetEnd = stop.getStopIndex();
        statement.setLineNumberStart(lineNumberStart);
        statement.setLineNumberStop(lineNumberStop);
        statement.setColNumberStart(colNumberStart);
        statement.setColNumberStop(colNumberStop);
        statement.setOffsetStart(offsetStart);
        statement.setOffsetEnd(offsetEnd);
        statement.setSourceText(textWithWS(ctx));
        statement.setCtx(ctx);
    }

    public void recordMetadata(ParserRuleContext ctx, CStatement statement) {
        if (!currentStatementContext.isEmpty()) {
            ctx =
                    currentStatementContext
                            .peek()
                            .get1(); // this will overwrite the current ASt element's ctx
            // with the statement's ctx
        }
        recordMetadataCommon(ctx, statement);
    }

    public void recordMetadata(ParserRuleContext ctx, CFunction statement) {
        if (!currentStatementContext.isEmpty()) {
            ctx =
                    currentStatementContext
                            .peek()
                            .get1(); // this will overwrite the current ASt element's ctx
            // with the statement's ctx
        }
        recordMetadataCommon(ctx, statement);
        // propagate function name to all statements
        propagateFunctionName(statement.getCompound(), statement.getFuncDecl().getName());
    }

    public void recordMetadata(ParserRuleContext ctx, CCall statement) {
        ctx = (ParserRuleContext) ctx.parent.parent;
        recordMetadataCommon(ctx, statement);
    }

    private void propagateFunctionName(CStatement stmt, String name) {
        if (stmt.getFunctionName() == null) {
            // only overwrite if null, because
            // sometimes we set it to "NotC" on purpose
            // and we do not want to overwrite that
            stmt.setFunctionName(name);
        }
        if (stmt instanceof CCompound) {
            ((CCompound) stmt)
                    .getcStatementList()
                    .forEach(cStatement -> propagateFunctionName(cStatement, name));
        }
    }

    @Override
    public CStatement visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
        List<CDeclaration> declarations =
                declarationVisitor.getDeclarations(
                        ctx.declaration().declarationSpecifiers(),
                        ctx.declaration().initDeclaratorList());
        CDecls decls = new CDecls(parseContext);
        for (CDeclaration declaration : declarations) {
            if (!declaration.getType().isTypedef()) {
                if (!declaration
                        .isFunc()) { // functions should not be interpreted as global variables
                    createVars(declaration);
                    for (VarDecl<?> varDecl : declaration.getVarDecls()) {
                        decls.getcDeclarations().add(Tuple2.of(declaration, varDecl));
                    }
                } else {
                    CSimpleType returnType = declaration.getType();
                    declaration.setType(returnType);
                    if (!variables.peek().get2().containsKey(declaration.getName())) {
                        parseContext
                                .getMetadata()
                                .create(declaration.getName(), "cType", returnType.getActualType());
                        createVars(declaration);
                        for (VarDecl<?> varDecl : declaration.getVarDecls()) {
                            functions.put(varDecl, declaration);
                        }
                    }
                }
            }
        }
        recordMetadata(ctx, decls);
        return decls;
    }

    @Override
    public CStatement visitFunctionDefinition(CParser.FunctionDefinitionContext ctx) {
        CSimpleType returnType = ctx.declarationSpecifiers().accept(typeVisitor);
        if (returnType.isTypedef()) return new CNullStatement(parseContext);
        CDeclaration funcDecl = ctx.declarator().accept(declarationVisitor);
        funcDecl.setType(returnType);
        if (!variables.peek().get2().containsKey(funcDecl.getName())) {
            parseContext
                    .getMetadata()
                    .create(funcDecl.getName(), "cType", returnType.getActualType());
            createVars(funcDecl);
        } else {
            // The function was declared before it was defined -- a prototype, which is how a C file
            // normally introduces one. The variable standing for its address belongs to *that*
            // declaration, so the definition must adopt it rather than be left with none: the id of
            // a function's address is initialised by walking the *definition's* variables, and an
            // empty list there meant the address was never initialised at all. A function pointer
            // then held an arbitrary value, every candidate's dispatch guard became satisfiable,
            // and
            // a call through it could land in any function of the right arity -- reporting a
            // counterexample through a callee the program can never reach.
            funcDecl.addVarDecl(variables.peek().get2().get(funcDecl.getName()));
        }
        for (VarDecl<?> varDecl : funcDecl.getVarDecls()) {
            functions.put(varDecl, funcDecl);
        }
        variables.push(Tuple2.of(funcDecl.getName(), new LinkedHashMap<>()));
        flatVariables.clear();
        for (CDeclaration functionParam : funcDecl.getFunctionParams()) {
            if (functionParam.getName() != null) createVars(functionParam);
        }
        CParser.BlockItemListContext blockItemListContext = ctx.compoundStatement().blockItemList();
        if (blockItemListContext != null) {
            CStatement accept = blockItemListContext.accept(this);
            variables.pop();
            CFunction cFunction =
                    new CFunction(
                            funcDecl,
                            accept,
                            new ArrayList<>(flatVariables),
                            parseContext,
                            atomicVariables);
            recordMetadata(ctx, cFunction);
            return cFunction;
        }
        variables.pop();
        CCompound cCompound = new CCompound(parseContext);
        CFunction cFunction =
                new CFunction(
                        funcDecl,
                        cCompound,
                        new ArrayList<>(flatVariables),
                        parseContext,
                        atomicVariables);
        recordMetadata(ctx, cCompound);
        recordMetadata(ctx, cFunction);
        return cFunction;
    }

    @Override
    public CStatement visitBlockItemList(CParser.BlockItemListContext ctx) {
        CCompound compound = new CCompound(parseContext);
        if (ctx.parent.parent.parent.parent instanceof CParser.BlockItemListContext)
            variables.push(Tuple2.of("anonymous" + anonCnt++, new LinkedHashMap<>()));
        for (CParser.BlockItemContext blockItemContext : ctx.blockItem()) {
            currentStatementContext.push(Tuple2.of(blockItemContext, Optional.of(compound)));
            compound.addCStatement(blockItemContext.accept(this));
            currentStatementContext.pop();
        }
        if (ctx.parent.parent.parent.parent instanceof CParser.BlockItemListContext)
            variables.pop();
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitIdentifierStatement(CParser.IdentifierStatementContext ctx) {
        CStatement statement = ctx.blockItem().accept(this);
        CCompound compound = new CCompound(parseContext);
        compound.addCStatement(statement);
        compound.setId(ctx.Identifier().getText());
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitCaseStatement(CParser.CaseStatementContext ctx) {
        parseContext.getCStmtCounter().incrementBranches();
        CExpr cexpr =
                new CExpr(
                        ctx.constantExpression()
                                .accept(
                                        new ExpressionVisitor(
                                                atomicVariables,
                                                parseContext,
                                                this,
                                                variables,
                                                functions,
                                                typedefVisitor,
                                                typeVisitor,
                                                uniqueWarningLogger)),
                        parseContext);
        CCase cCase = new CCase(cexpr, ctx.statement().accept(this), parseContext);
        recordMetadata(ctx, cCase);
        recordMetadata(ctx.constantExpression(), cexpr);
        return cCase;
    }

    @Override
    public CStatement visitDefaultStatement(CParser.DefaultStatementContext ctx) {
        CDefault cDefault = new CDefault(ctx.statement().accept(this), parseContext);
        recordMetadata(ctx, cDefault);
        return cDefault;
    }

    @Override
    public CStatement visitCompoundStatement(CParser.CompoundStatementContext ctx) {
        if (ctx.blockItemList() != null) {
            return ctx.blockItemList().accept(this);
        }
        CCompound compound = new CCompound(parseContext);
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitExpressionStatement(CParser.ExpressionStatementContext ctx) {
        CStatement statement =
                ctx.expression() == null
                        ? new CNullStatement(parseContext)
                        : ctx.expression().accept(this);
        recordMetadata(ctx, statement);
        return statement;
    }

    @Override
    public CStatement visitIfStatement(CParser.IfStatementContext ctx) {
        parseContext.getCStmtCounter().incrementBranches();
        variables.push(Tuple2.of("if" + anonCnt++, new LinkedHashMap<>()));
        CStatement condition = ctx.expression().accept(this);
        // Each arm is a scope of its own. A brace-enclosed arm does not open one itself --
        // `visitBlockItemList` only does that for a block nested directly in another block -- so
        // without this both arms share the `if` scope, and a name declared in both is one variable
        // wearing two C types: the second declaration finds the first in the scope map, reuses its
        // VarDecl, and then overwrites the recorded `cType`. Every use, in *either* arm, is then
        // typed by whichever arm was visited last. `if (c) { uint64_t a; } else { uint32_t a; }` --
        // how aws-c-common writes its 64/32-bit harness pairs -- so narrows the 64-bit arm to 32
        // bits: its values silently stop being able to exceed 2^32, which both hides real bugs and
        // breaks the arithmetic the other arm asserts.
        CStatement thenArm = inOwnScope("then", ctx.statement(0));
        CStatement elseArm =
                ctx.statement().size() > 1 ? inOwnScope("else", ctx.statement(1)) : null;
        CIf cIf = new CIf(condition, thenArm, elseArm, parseContext);
        recordMetadata(ctx, cIf);
        variables.pop();
        return cIf;
    }

    /**
     * Visits a statement with a scope of its own, so its declarations cannot collide with a
     * sibling's.
     */
    private CStatement inOwnScope(String kind, CParser.StatementContext statement) {
        variables.push(Tuple2.of(kind + anonCnt++, new LinkedHashMap<>()));
        try {
            return statement.accept(this);
        } finally {
            variables.pop();
        }
    }

    @Override
    public CStatement visitSwitchStatement(CParser.SwitchStatementContext ctx) {
        variables.push(Tuple2.of("switch" + anonCnt++, new LinkedHashMap<>()));
        CSwitch cSwitch =
                new CSwitch(
                        ctx.expression().accept(this), ctx.statement().accept(this), parseContext);
        recordMetadata(ctx, cSwitch);
        variables.pop();
        return cSwitch;
    }

    @Override
    public CStatement visitWhileStatement(CParser.WhileStatementContext ctx) {
        parseContext.getCStmtCounter().incrementWhileLoops();
        variables.push(Tuple2.of("while" + anonCnt++, new LinkedHashMap<>()));
        CWhile cWhile =
                new CWhile(
                        ctx.statement().accept(this), ctx.expression().accept(this), parseContext);
        recordMetadata(ctx, cWhile);
        variables.pop();
        return cWhile;
    }

    @Override
    public CStatement visitDoWhileStatement(CParser.DoWhileStatementContext ctx) {
        variables.push(Tuple2.of("dowhile" + anonCnt++, new LinkedHashMap<>()));
        CDoWhile cDoWhile =
                new CDoWhile(
                        ctx.statement().accept(this), ctx.expression().accept(this), parseContext);
        recordMetadata(ctx, cDoWhile);
        variables.pop();
        return cDoWhile;
    }

    @Override
    public CStatement visitForStatement(CParser.ForStatementContext ctx) {
        parseContext.getCStmtCounter().incrementForLoops();
        variables.push(Tuple2.of("for" + anonCnt++, new LinkedHashMap<>()));
        CStatement init = ctx.forCondition().forInit().accept(this);
        CStatement test = ctx.forCondition().forTest().accept(this);
        if (test == null) {
            CCompound newCCompound1 = new CCompound(parseContext);
            CCompound newCCompound2 = new CCompound(parseContext);
            CCompound newCCompound3 = new CCompound(parseContext);
            CCompound newCCompound4 = new CCompound(parseContext);
            newCCompound1.addCStatement(newCCompound2);
            Expr<?> one = CComplexType.getSignedInt(parseContext).getUnitValue();
            parseContext
                    .getMetadata()
                    .create(one, "cType", CComplexType.getSignedInt(parseContext));
            newCCompound2.addCStatement(new CExpr(one, parseContext));
            newCCompound2.setPreStatements(newCCompound3);
            newCCompound2.setPostStatements(newCCompound4);
            test = newCCompound1;
            recordMetadata(ctx.forCondition(), test);
        }
        CStatement incr = ctx.forCondition().forIncr().accept(this);
        CFor cFor = new CFor(ctx.statement().accept(this), init, test, incr, parseContext);
        recordMetadata(ctx, cFor);
        variables.pop();
        return cFor;
    }

    @Override
    public CStatement visitGotoStatement(CParser.GotoStatementContext ctx) {
        CGoto cGoto = new CGoto(ctx.Identifier().getText(), parseContext);
        recordMetadata(ctx, cGoto);
        return cGoto;
    }

    @Override
    public CStatement visitContinueStatement(CParser.ContinueStatementContext ctx) {
        CContinue cContinue = new CContinue(parseContext);
        recordMetadata(ctx, cContinue);
        return cContinue;
    }

    @Override
    public CStatement visitBreakStatement(CParser.BreakStatementContext ctx) {
        CBreak cBreak = new CBreak(parseContext);
        recordMetadata(ctx, cBreak);
        return cBreak;
    }

    @Override
    public CStatement visitReturnStatement(CParser.ReturnStatementContext ctx) {
        CRet cRet =
                new CRet(
                        ctx.expression() == null ? null : ctx.expression().accept(this),
                        parseContext);
        recordMetadata(ctx, cRet);
        return cRet;
    }

    @Override
    public CStatement visitStatement(CParser.StatementContext ctx) {
        currentStatementContext.push(Tuple2.of(ctx, Optional.empty()));
        // Every other alternative of `statement` starts with a sub-rule; only the inline-assembly
        // one starts with a keyword token, and its children would visit to null.
        final var ret =
                isInlineAssembly(ctx) ? inlineAssembly(ctx) : ctx.children.get(0).accept(this);
        currentStatementContext.pop();
        return ret;
    }

    private static final Set<String> ASM_KEYWORDS = Set.of("asm", "__asm", "__asm__");

    private static boolean isInlineAssembly(CParser.StatementContext ctx) {
        return ctx.children.get(0) instanceof TerminalNode keyword
                && ASM_KEYWORDS.contains(keyword.getText());
    }

    /**
     * Models an inline assembly statement, which the analysis cannot execute.
     *
     * <p>An empty assembly template is not machine code at all but a compiler barrier (e.g. {@code
     * __asm__ __volatile__("" : "+r"(x))}, which only stops the value from being optimized away):
     * it leaves its operands untouched, so it is modelled exactly, as a no-op.
     *
     * <p>A non-empty template really does execute, and typically writes to its output operands
     * (e.g. {@code __asm__("movq %%gs:%P1,%0" : "=r"(v) : ...)}). Since we cannot say what it
     * computes, each output operand is havoced -- an over-approximation, which keeps the analysis
     * sound -- and any other effect it may have (on memory, on inputs marked read-write) is warned
     * about, as it is silently dropped.
     */
    private CStatement inlineAssembly(CParser.StatementContext ctx) {
        CCompound compound = new CCompound(parseContext);
        if (isEmptyAssemblyTemplate(ctx)) {
            recordMetadata(ctx, compound);
            return compound;
        }
        uniqueWarningLogger.write(
                Level.INFO,
                "WARNING: inline assembly is not interpreted; its output operands are havoced and"
                        + " its other side-effects are ignored.\n");
        for (CParser.LogicalOrExpressionContext operand : outputOperands(ctx)) {
            CStatement lValue = operandLValue(operand);
            if (lValue == null) {
                continue;
            }
            CComplexType type = CComplexType.getType(lValue.getExpression(), parseContext);
            // A `__VERIFIER_nondet*` call is turned into a havoc of its return value by
            // NondetFunctionPass; the name must not collide with a function the program defines.
            parseContext.getMetadata().create(ASM_NONDET, "cType", type);
            CCall nondet = new CCall(ASM_NONDET, List.of(), parseContext);
            compound.addCStatement(nondet);
            CAssignment assignment =
                    new CAssignment(
                            lValue.getExpression(),
                            new CExpr(nondet.getRet().getRef(), parseContext),
                            "=",
                            parseContext);
            recordMetadata(ctx, assignment);
            compound.addCStatement(assignment);
        }
        if (compound.getcStatementList().isEmpty()) {
            compound.addCStatement(new CNullStatement(parseContext));
        }
        recordMetadata(ctx, compound);
        return compound;
    }

    private static final String ASM_NONDET = "__VERIFIER_nondet_theta_asm";

    /**
     * The assembly template: every token between the opening parenthesis and the first colon (an
     * assembly template may be written as several adjacent string literals). Empty exactly when
     * every one of them is the empty string.
     */
    private boolean isEmptyAssemblyTemplate(CParser.StatementContext ctx) {
        for (ParseTree child : ctx.children) {
            String text = child.getText();
            if (text.equals(":") || text.equals(")")) {
                break;
            }
            if (child instanceof CParser.LogicalOrExpressionContext
                    && !text.replace("\"", "").isBlank()) {
                return false;
            }
        }
        return true;
    }

    /** The operands of the first colon group, which are the outputs. */
    private List<CParser.LogicalOrExpressionContext> outputOperands(CParser.StatementContext ctx) {
        List<CParser.LogicalOrExpressionContext> operands = new ArrayList<>();
        int colons = 0;
        for (ParseTree child : ctx.children) {
            if (child.getText().equals(":")) {
                colons++;
                if (colons > 1) {
                    break;
                }
            } else if (colons == 1 && child instanceof CParser.LogicalOrExpressionContext operand) {
                operands.add(operand);
            }
        }
        return operands;
    }

    /**
     * The lvalue an output operand writes to: an operand is a constraint string applied to a
     * parenthesized expression (`"=r" (x)`), which parses as if the string literal were called with
     * the lvalue as its argument. Returns null if the operand does not have that shape.
     */
    private CStatement operandLValue(CParser.LogicalOrExpressionContext operand) {
        CParser.ArgumentExpressionListContext arguments =
                firstDescendant(operand, CParser.ArgumentExpressionListContext.class);
        if (arguments == null || arguments.assignmentExpression().isEmpty()) {
            return null;
        }
        return arguments.assignmentExpression(0).accept(this);
    }

    private static <T extends ParseTree> T firstDescendant(ParseTree node, Class<T> type) {
        for (int i = 0; i < node.getChildCount(); i++) {
            ParseTree child = node.getChild(i);
            if (type.isInstance(child)) {
                return type.cast(child);
            }
            T found = firstDescendant(child, type);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /**
     * Emits `v = <initializer>` for a declaration that has one, and lifts whatever the initializer
     * itself has to run: a call arrives as a compound whose pre-statements hold the call, and those
     * have to be hoisted ahead of the assignment or the call never happens.
     */
    /**
     * The cell an initializer-list element writes: its stored designated position when present (the
     * frontend resolves designators to positions), otherwise the running position.
     */
    private LitExpr<?> initPosition(
            Optional<CStatement> designator, CComplexType ptrType, LitExpr<?> runningPosition) {
        if (designator.isEmpty()) {
            return runningPosition;
        }
        final IntLitExpr position = (IntLitExpr) designator.get().getExpression();
        return (LitExpr<?>) ptrType.getValue(position.getValue().toString());
    }

    /**
     * The cell index a designator selects, as a plain int, or {@code fallback} when there is none.
     * The int mirror of {@link #initPosition}, kept beside it so the two cannot drift.
     */
    private int designatedPosition(Optional<CStatement> designator, int fallback) {
        if (designator.isEmpty()) {
            return fallback;
        }
        return ((IntLitExpr) designator.get().getExpression()).getValue().intValueExact();
    }

    /**
     * The declared type of cell {@code offset} of {@code type}, mirroring
     * FrontendXcfaBuilder#cellTypeAt, which the same-shaped global initializer uses. Needed to give
     * a zero-fill assignment the cell's own type.
     */
    private CComplexType cellTypeAt(CComplexType type, int offset) {
        if (type instanceof CArray cArrayType) {
            final CComplexType elem = cArrayType.getEmbeddedType();
            final int stride = cellsOf(elem);
            return cellTypeAt(elem, stride > 0 ? offset % stride : 0);
        }
        if (type instanceof CStruct cStructType && !cStructType.isUnion()) {
            for (Tuple2<String, CComplexType> field : cStructType.getFields()) {
                final int unit = cStructType.unitOffsetOf(field.get1());
                if (offset >= unit && offset < unit + cellsOf(field.get2())) {
                    return cellTypeAt(field.get2(), offset - unit);
                }
            }
        }
        return type;
    }

    /**
     * Writes zero into every cell of {@code declaration}'s storage that {@code written} does not
     * cover.
     *
     * <p>C11 6.7.9p21: when an aggregate has an initializer but fewer entries than it has members,
     * the remainder is initialized as if it had static storage duration -- i.e. zero. The global
     * path already does this; a *local* one wrote only the cells the braces mention and left the
     * rest unconstrained, so `float a[4] = {0}` gave cells 1..3 arbitrary values and the solver was
     * free to invent a counterexample out of them.
     */
    private void zeroFillRemainingCells(
            CComplexType actualType,
            Set<Integer> written,
            CComplexType ptrType,
            VarDecl<?> varDecl,
            CCompound compound,
            CParser.BodyDeclarationContext ctx) {
        final int total = cellsOf(actualType);
        for (int index = 0; index < total; index++) {
            if (written.contains(index)) {
                continue;
            }
            final CComplexType cellType = cellTypeAt(actualType, index);
            final var offset = ptrType.getValue(String.valueOf(index));
            final var deref =
                    Exprs.Dereference(
                            cast(varDecl.getRef(), offset.getType()),
                            cast(offset, offset.getType()),
                            cellType.getSmtType());
            final CAssignment cAssignment =
                    new CAssignment(
                            deref, new CExpr(cellType.getNullValue(), parseContext), "=",
                            parseContext);
            recordMetadata(ctx, cAssignment);
            compound.addCStatement(cAssignment);
        }
    }

    private void emitInitAssignment(
            CParser.BodyDeclarationContext ctx,
            CDeclaration declaration,
            CCompound compound,
            CCompound preCompound,
            CCompound postCompound) {
        CAssignment cAssignment =
                new CAssignment(
                        declaration.getVarDecls().get(0).getRef(),
                        declaration.getInitExpr(),
                        "=",
                        parseContext);
        recordMetadata(ctx, cAssignment);
        compound.addCStatement(cAssignment);
        if (declaration.getInitExpr() instanceof CCompound compoundInitExpr) {
            final var preStatements = collectPreStatements(compoundInitExpr);
            preStatements.forEach(preCompound::addCStatement);
            final var postStatements = collectPostStatements(compoundInitExpr);
            postStatements.forEach(postCompound::addCStatement);
            resetPreStatements(compoundInitExpr);
            resetPostStatements(compoundInitExpr);
        }
    }

    /**
     * How many storage cells one value of {@code type} occupies in the flat cell-indexed model
     * this initializer loop uses (one cell per scalar field/element); mirrors
     * FrontendXcfaBuilder#cellsOf, which the same-shaped global initializer uses.
     */
    private int cellsOf(CComplexType type) {
        if (type instanceof CArray cArrayType) {
            final Integer dimension = ObjectLayout.constantDimension(cArrayType);
            final int count = dimension == null ? 1 : dimension;
            return count * cellsOf(cArrayType.getEmbeddedType());
        } else if (type instanceof CStruct cStructType) {
            if (cStructType.isUnion()) {
                final Integer width = cStructType.unionCellWidth();
                return width == null
                        ? ObjectLayout.of(cStructType, parseContext.getArchitecture()).bitSize()
                                / 8
                        : 1;
            }
            return cStructType.getUnitCount();
        } else {
            return 1;
        }
    }

    /**
     * The declared type of the {@code index}-th member of an aggregate {@code parentType}: an
     * array's (uniform) embedded type, or a struct's {@code index}-th field, positionally --
     * designators aside, this matches how the surrounding loop already indexes cells. Needed only
     * to size a further-nested initializer list; a plain scalar list entry never consults it.
     */
    private CComplexType subElementTypeOf(CComplexType parentType, int index) {
        if (parentType instanceof CArray cArrayType) {
            return cArrayType.getEmbeddedType();
        } else if (parentType instanceof CStruct cStructType) {
            final List<Tuple2<String, CComplexType>> fields = cStructType.getFields();
            if (fields.isEmpty()) {
                return parentType;
            }
            // A union's members overlap at offset 0; every entry addresses the same storage.
            final int i = cStructType.isUnion() ? 0 : Math.min(index, fields.size() - 1);
            return fields.get(i).get2();
        }
        return parentType;
    }

    /**
     * Emits one cell-assignment per scalar leaf of a (possibly nested) initializer-list value,
     * starting at {@code baseOffset} cells within {@code varDecl}'s storage. {@code elementType}
     * is the declared type of one unit at this nesting level -- only consulted when {@code value}
     * turns out to be itself a nested {@link CInitializerList}, to size that nested group's cells.
     * A plain scalar {@code value} (the pre-existing, non-nested case) is handled exactly as
     * before: one cell, using the value's own type for the dereference.
     */
    private void flattenInitializer(
            CStatement value,
            CComplexType elementType,
            LitExpr<?> baseOffset,
            VarDecl<?> varDecl,
            CComplexType ptrType,
            CCompound compound,
            CParser.BodyDeclarationContext ctx) {
        flattenInitializer(
                value, elementType, baseOffset, varDecl, ptrType, compound, ctx, 0, null);
    }

    /**
     * As above, but also records which cells the initializer actually writes. {@code baseIndex} is
     * {@code baseOffset}'s numeric value, carried in parallel so the cell index never has to be
     * decoded back out of a typed literal, and {@code written} collects them (null to not collect).
     */
    private void flattenInitializer(
            CStatement value,
            CComplexType elementType,
            LitExpr<?> baseOffset,
            VarDecl<?> varDecl,
            CComplexType ptrType,
            CCompound compound,
            CParser.BodyDeclarationContext ctx,
            int baseIndex,
            Set<Integer> written) {
        if (value instanceof CInitializerList nestedList) {
            LitExpr<?> offset = ptrType.getNullValue();
            int offsetIndex = 0;
            int index = 0;
            for (Tuple2<Optional<CStatement>, CStatement> entry : nestedList.getStatements()) {
                final LitExpr<?> before = offset;
                offset = initPosition(entry.get1(), ptrType, offset);
                // A designator jumps the cursor; recover the jump as an int the same way the
                // literal path does, so the parallel index stays in step with the literal offset.
                if (offset != before && entry.get1().isPresent()) {
                    offsetIndex = designatedPosition(entry.get1(), offsetIndex);
                }
                final CComplexType subType = subElementTypeOf(elementType, index);
                final LitExpr<?> cellOffset =
                        (LitExpr<?>) Add(baseOffset, offset).eval(ImmutableValuation.empty());
                flattenInitializer(
                        entry.get2(),
                        subType,
                        cellOffset,
                        varDecl,
                        ptrType,
                        compound,
                        ctx,
                        baseIndex + offsetIndex,
                        written);
                offset =
                        (LitExpr<?>)
                                Add(offset, ptrType.getValue(String.valueOf(cellsOf(subType))))
                                        .eval(ImmutableValuation.empty());
                offsetIndex += cellsOf(subType);
                index++;
            }
        } else {
            if (written != null) {
                written.add(baseIndex);
            }
            final var expr = value.getExpression();
            final var deref =
                    Exprs.Dereference(
                            cast(varDecl.getRef(), baseOffset.getType()),
                            cast(baseOffset, baseOffset.getType()),
                            expr.getType());
            CAssignment cAssignment = new CAssignment(deref, value, "=", parseContext);
            recordMetadata(ctx, cAssignment);
            compound.addCStatement(cAssignment);
        }
    }

    @Override
    public CStatement visitBodyDeclaration(CParser.BodyDeclarationContext ctx) {
        List<CDeclaration> declarations =
                declarationVisitor.getDeclarations(
                        ctx.declaration().declarationSpecifiers(),
                        ctx.declaration().initDeclaratorList());
        CCompound compound = new CCompound(parseContext);
        final var preCompound = new CCompound(parseContext);
        final var postCompound = new CCompound(parseContext);
        compound.setPreStatements(preCompound);
        compound.setPostStatements(postCompound);
        for (CDeclaration declaration : declarations) {
            createVars(declaration);
            if (declaration.getActualType() instanceof CArray cArray) {
                // A stack array is an `alloca`, not a `malloc`+`free`. Both give it a fresh runtime
                // base -- so, unlike the old compile-time base, two activations of the function
                // (recursion, threads) cannot alias -- but `alloca` is the honest model: its memory
                // is released when the function returns, not by the program, so it lands in the
                // free residue class and is neither a leak the program must clean up nor freeable.
                // The old free at scope exit modelled it as heap, which reported a bogus
                // double-free
                // for a returned-and-reused block and a bogus leak when the scope was a loop body.
                parseContext
                        .getMetadata()
                        .create(
                                "alloca",
                                "cType",
                                new CPointer(null, cArray.getEmbeddedType(), parseContext));
                // The block has to span the array's *flat cells*, not its element count: `a[i].f`
                // is addressed as `a[i * unitCount + f]` (see ExpressionVisitor#rowOf), so an
                // element occupying several cells makes the object that many times longer. Passing
                // the bare dimension recorded a size smaller than the object's own addressable
                // range, and every access past the first element then satisfied the valid-deref
                // bound `size <= offset` -- `struct Item arr[3]` was recorded as 3 cells for a
                // 6-cell object.
                //
                // Built as an expression, not folded to an int: the dimension may be a VLA's
                // runtime value, so the scale factor is multiplied in rather than computed here.
                final int elementCells = cellsOf(cArray.getEmbeddedType());
                CStatement allocaSize = cArray.getArrayDimension();
                if (elementCells != 1) {
                    final var dimExpr = allocaSize.getExpression();
                    final CComplexType dimType = CComplexType.getType(dimExpr, parseContext);
                    final var scaled =
                            AbstractExprs.Mul(
                                    dimType.castTo(dimExpr),
                                    dimType.getValue(String.valueOf(elementCells)));
                    parseContext.getMetadata().create(scaled, "cType", dimType);
                    allocaSize = new CExpr(scaled, parseContext);
                }
                final var alloca = new CCall("alloca", List.of(allocaSize), parseContext);
                preCompound.addCStatement(alloca);
                CAssignment cAssignment =
                        new CAssignment(
                                declaration.getVarDecls().get(0).getRef(),
                                new CExpr(alloca.getRet().getRef(), parseContext),
                                "=",
                                parseContext);
                recordMetadata(ctx, cAssignment);
                compound.addCStatement(cAssignment);
            }
            if (declaration.getInitExpr() != null) {
                if (declaration.getActualType() instanceof CStruct) {
                    if (declaration.getInitExpr() instanceof CInitializerList) {
                        final var initializerList = (CInitializerList) declaration.getInitExpr();
                        List<VarDecl<?>> varDecls = declaration.getVarDecls();
                        VarDecl<?> varDecl = varDecls.get(0);
                        final var ptrType = CComplexType.getUnsignedLong(parseContext);
                        final var structType = (CStruct) declaration.getActualType();
                        LitExpr<?> currentValue = ptrType.getNullValue();
                        int fieldIndex = 0;
                        for (Tuple2<Optional<CStatement>, CStatement> statement :
                                initializerList.getStatements()) {
                            currentValue = initPosition(statement.get1(), ptrType, currentValue);
                            final CComplexType elementType =
                                    subElementTypeOf(structType, fieldIndex);
                            flattenInitializer(
                                    statement.get2(),
                                    elementType,
                                    currentValue,
                                    varDecl,
                                    ptrType,
                                    compound,
                                    ctx);
                            currentValue =
                                    Add(
                                                    currentValue,
                                                    ptrType.getValue(
                                                            String.valueOf(cellsOf(elementType))))
                                            .eval(ImmutableValuation.empty());
                            fieldIndex++;
                        }
                    } else {
                        Expr<?> expression = declaration.getInitExpr().getExpression();
                        final var initType = CComplexType.getType(expression, parseContext);
                        if (expression instanceof RefExpr<?>
                                || expression instanceof Dereference<?, ?, ?>
                                || initType instanceof CStruct) {
                            // A struct value is its base id, whether read from a variable or out of
                            // another object's cell: `struct S s = *p;` and `= o.field` copy the same
                            // way `= other;` does.
                            checkState(
                                    initType instanceof CStruct,
                                    "Initializer type not handled for structs: " + expression);
                            checkState(
                                    initType.equals(declaration.getActualType()),
                                    "Mismatching types: "
                                            + initType
                                            + " vs. "
                                            + declaration.getActualType());
                            // Checking the types is not initialising the variable: this branch used
                            // to stop here, so `struct S s = other;` declared `s` and then quietly
                            // never copied anything into it, leaving every field of `s`
                            // unconstrained. The solver could then read whatever it liked out of
                            // `s`. The shape is not exotic -- it is what a struct-returning function
                            // looks like at the call site (`struct aws_byte_buf buf =
                            // aws_byte_buf_from_array(a, len);`), so the aws-c-common
                            // byte_buf/byte_cursor harnesses all asserted on an uninitialised struct
                            // and false-alarmed. The plain statement form (`s = other;`) always
                            // worked, so emit exactly that, as the non-struct branch below does.
                            emitInitAssignment(
                                    ctx, declaration, compound, preCompound, postCompound);
                        } else {
                            // A struct/union initialised with a *scalar* (`union U u = raw;`, the
                            // register-overlay idiom the intel-tdx-module firmware uses): C
                            // initialises the object's first member, so write the value into its
                            // first cell (offset 0), exactly as `= { raw }` would. Refusing this used
                            // to fail parsing outright ("Initializer type not handled").
                            final VarDecl<?> varDecl = declaration.getVarDecls().get(0);
                            final var ptrType = CComplexType.getUnsignedLong(parseContext);
                            final LitExpr<?> zero = ptrType.getNullValue();
                            final var deref =
                                    Exprs.Dereference(
                                            cast(varDecl.getRef(), zero.getType()),
                                            cast(zero, zero.getType()),
                                            expression.getType());
                            CAssignment cAssignment =
                                    new CAssignment(
                                            deref, declaration.getInitExpr(), "=", parseContext);
                            recordMetadata(ctx, cAssignment);
                            compound.addCStatement(cAssignment);
                        }
                    }
                } else {
                    checkState(
                            declaration.getVarDecls().size() == 1,
                            "non-struct declarations shall only have one variable!");
                    if (declaration.getInitExpr() instanceof CInitializerList initializerList) {
                        final var ptrType = CComplexType.getUnsignedLong(parseContext);
                        final var varDecl = declaration.getVarDecls().get(0);
                        // Uniform across entries: an array's (single) embedded type, or -- for the
                        // degenerate `int x = {5};` / `{{5}}` braced-scalar case, where the
                        // declared type is not a CArray at all -- the scalar type itself (only
                        // consulted if an entry turns out to be a further-nested list).
                        final CComplexType elementType =
                                declaration.getActualType() instanceof CArray cArrayType
                                        ? cArrayType.getEmbeddedType()
                                        : declaration.getActualType();
                        LitExpr<?> currentValue = ptrType.getNullValue();
                        final Set<Integer> written = new LinkedHashSet<>();
                        int currentIndex = 0;
                        for (Tuple2<Optional<CStatement>, CStatement> statement :
                                initializerList.getStatements()) {
                            currentValue = initPosition(statement.get1(), ptrType, currentValue);
                            currentIndex = designatedPosition(statement.get1(), currentIndex);
                            flattenInitializer(
                                    statement.get2(),
                                    elementType,
                                    currentValue,
                                    varDecl,
                                    ptrType,
                                    compound,
                                    ctx,
                                    currentIndex,
                                    written);
                            currentValue =
                                    Add(
                                                    currentValue,
                                                    ptrType.getValue(
                                                            String.valueOf(cellsOf(elementType))))
                                            .eval(ImmutableValuation.empty());
                            currentIndex += cellsOf(elementType);
                        }
                        // C11 6.7.9p21: the members the braces do not reach are zero, exactly as
                        // the global path already does. Emitted after the explicit writes and only
                        // for the cells they missed, so a fully-specified initializer costs nothing.
                        zeroFillRemainingCells(
                                declaration.getActualType(),
                                written,
                                ptrType,
                                varDecl,
                                compound,
                                ctx);
                    } else {
                        emitInitAssignment(ctx, declaration, compound, preCompound, postCompound);
                    }
                }
            } else {
                // if there is no initializer, then we'll add an assumption regarding min and max
                // values
                if (declaration.getActualType() instanceof CStruct) {
                    for (VarDecl<?> varDecl : declaration.getVarDecls()) {
                        if (!(varDecl.getType() instanceof ArrayType)
                                && !(varDecl.getType()
                                        instanceof
                                        BoolType)) { // BoolType is either well-defined true/false,
                            // or a struct in disguise
                            AssumeStmt assumeStmt =
                                    CComplexType.getType(varDecl.getRef(), parseContext)
                                            .limit(varDecl.getRef());
                            CAssume cAssume = new CAssume(assumeStmt, parseContext);
                            recordMetadata(ctx, cAssume);
                            cAssume.setFunctionName("NotC");
                            // as assumption is not in C
                            // file
                            compound.addCStatement(cAssume);
                        }
                    }
                } else {
                    VarDecl<?> varDecl = declaration.getVarDecls().get(0);
                    if (!(varDecl.getType() instanceof ArrayType)
                            && !(varDecl.getType() instanceof BoolType)
                            && !(CComplexType.getType(varDecl.getRef(), parseContext)
                                    instanceof CVoid)) {
                        AssumeStmt assumeStmt =
                                CComplexType.getType(varDecl.getRef(), parseContext)
                                        .limit(varDecl.getRef());
                        CAssume cAssume = new CAssume(assumeStmt, parseContext);
                        recordMetadata(ctx, cAssume);
                        cAssume.setFunctionName("NotC");
                        // assumption is not in C file
                        compound.addCStatement(cAssume);
                    }
                }
            }
        }
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitExpression(CParser.ExpressionContext ctx) {
        CCompound compound = new CCompound(parseContext);
        for (CParser.AssignmentExpressionContext assignmentExpressionContext :
                ctx.assignmentExpression()) {
            compound.addCStatement(assignmentExpressionContext.accept(this));
        }
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitAssignmentExpressionAssignmentExpression(
            CParser.AssignmentExpressionAssignmentExpressionContext ctx) {
        ExpressionVisitor expressionVisitor =
                new ExpressionVisitor(
                        atomicVariables,
                        parseContext,
                        this,
                        variables,
                        functions,
                        typedefVisitor,
                        typeVisitor,
                        uniqueWarningLogger);
        CCompound compound = new CCompound(parseContext);
        CCompound preStatements = new CCompound(parseContext);
        CCompound postStatements = new CCompound(parseContext);
        Expr<?> ret = ctx.unaryExpression().accept(expressionVisitor);
        CStatement rhs = ctx.assignmentExpression().accept(this);
        if (rhs instanceof CCompound compoundInitExpr) {
            final var preStatementList = collectPreStatements(compoundInitExpr);
            preStatementList.forEach(preStatements::addCStatement);
            final var postStatementList = collectPostStatements(compoundInitExpr);
            postStatementList.forEach(postStatements::addCStatement);
            resetPreStatements(compoundInitExpr);
            resetPostStatements(compoundInitExpr);
        }
        CAssignment cAssignment =
                new CAssignment(ret, rhs, ctx.assignmentOperator().getText(), parseContext);
        recordMetadata(ctx, cAssignment);
        expressionVisitor.getPreStatements().forEach(preStatements::addCStatement);
        compound.addCStatement(cAssignment);
        compound.setPreStatements(preStatements);
        recordMetadata(ctx, compound);
        expressionVisitor.getPostStatements().forEach(postStatements::addCStatement);
        compound.setPostStatements(postStatements);
        // The value of an assignment expression is the value assigned, taken at the assignment --
        // not
        // a later re-read of the destination. When the expression has deferred side effects -- a
        // post-increment, as in `*s1++ = *s2++` -- the destination lvalue `*s1` moves before the
        // value
        // is consumed, so re-reading it (which is what `getExpression()` does) reads the wrong
        // cell.
        // `while ((*s1++ = *s2++))` then tested `*s1` at the advanced pointer, i.e. uninitialised
        // memory, instead of the assigned char, ran on and walked off the buffer (the
        // openbsd/strcpy
        // alloca `valid-deref` false alarms). Snapshot the value here, after the store and before
        // the
        // post-statements, and make it the compound's value. Assignments without side effects are
        // untouched (a plain `a = b` re-read is harmless), so the common case is unchanged.
        if (!postStatements.getcStatementList().isEmpty()) {
            Expr<?> assignedValue = cAssignment.getExpression();
            VarDecl<?> snapshot =
                    createTempVar(
                            CComplexType.getType(assignedValue, parseContext), "assignedvalue");
            compound.addCStatement(
                    new CAssignment(
                            snapshot.getRef(),
                            new CExpr(assignedValue, parseContext),
                            "=",
                            parseContext));
        }
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitAssignmentExpressionConditionalExpression(
            CParser.AssignmentExpressionConditionalExpressionContext ctx) {
        return ctx.conditionalExpression().accept(this);
    }

    private void resetPreStatements(CStatement statement) {
        if (statement instanceof CCompound compound) {
            compound.setPreStatements(null);
            for (CStatement cStatement : compound.getcStatementList()) {
                resetPreStatements(cStatement);
            }
        }
    }

    private void resetPostStatements(CStatement statement) {
        if (statement instanceof CCompound compound) {
            compound.setPostStatements(null);
            for (CStatement cStatement : compound.getcStatementList()) {
                resetPostStatements(cStatement);
            }
        }
    }

    private List<CStatement> getStatementList(CStatement statement) {
        if (statement instanceof CCompound compound) {
            return compound.getcStatementList().stream()
                    .flatMap(i -> getStatementList(i).stream())
                    .toList();
        } else if (statement != null) {
            return List.of(statement);
        } else {
            return List.of();
        }
    }

    /*
    This collects the following:
        - the current compound's pre-statement
        - all pre-statements of the pre-statement (before the pre-statement)
        - all the pre-statement of every cStatement
     */
    private List<CStatement> collectPreStatements(CStatement cStatement) {
        if (cStatement instanceof CCompound) {
            return Stream.concat(
                            Stream.concat(
                                    collectPreStatements(cStatement.getPreStatements()).stream(),
                                    getStatementList(cStatement.getPreStatements()).stream()),
                            ((CCompound) cStatement)
                                    .getcStatementList().stream()
                                            .flatMap(
                                                    cStatement1 ->
                                                            collectPreStatements(cStatement1)
                                                                    .stream()))
                    .filter(i -> !(i instanceof CExpr))
                    .toList();
        } else return List.of();
    }

    /*
    This collects the following:
        - all the post-statements of every cStatement
        - the current compound's post-statement
        - all post-statements of the post-statement (after the post-statement)
     */
    private List<CStatement> collectPostStatements(CStatement cStatement) {
        if (cStatement instanceof CCompound) {
            return Stream.concat(
                            ((CCompound) cStatement)
                                    .getcStatementList().stream()
                                            .flatMap(
                                                    cStatement1 ->
                                                            collectPostStatements(cStatement1)
                                                                    .stream()),
                            Stream.concat(
                                    getStatementList(cStatement.getPostStatements()).stream(),
                                    collectPostStatements(cStatement.getPostStatements()).stream()))
                    .filter(i -> !(i instanceof CExpr))
                    .toList();
        } else return List.of();
    }

    // This is in the function visitor, not in the expression visitor, because
    //    cond ? f1() : f2()
    // will only call either f1 or f2 (it can be used for branching)
    @Override
    public CStatement visitConditionalExpression(CParser.ConditionalExpressionContext ctx) {
        CCompound compound = new CCompound(parseContext);
        CCompound preStatements = new CCompound(parseContext);
        CCompound postStatements = new CCompound(parseContext);

        ExpressionVisitor expressionVisitor =
                new ExpressionVisitor(
                        atomicVariables,
                        parseContext,
                        this,
                        variables,
                        functions,
                        typedefVisitor,
                        typeVisitor,
                        uniqueWarningLogger);

        Expr<?> iteExpr;
        if (!ctx.expression().isEmpty()) {
            // GNU `a ?: b`: the middle operand is omitted, its value is the guard itself.
            CStatement ifTrue = ctx.ifTrue == null ? null : ctx.ifTrue.accept(this);
            CStatement ifFalse = ctx.ifFalse.accept(this);

            Expr<?> expr = ctx.logicalOrExpression().accept(expressionVisitor);
            Expr<?> lhs = ifTrue == null ? expr : ifTrue.getExpression();
            Expr<?> rhs = ifFalse.getExpression();

            CCompound guardCompound = new CCompound(parseContext);
            guardCompound.addCStatement(new CExpr(expr, parseContext));
            guardCompound.setPostStatements(new CNullStatement(parseContext));
            guardCompound.setPreStatements(new CNullStatement(parseContext));

            CCompound ifTruePre = new CCompound(parseContext);
            List<CStatement> ifTruePreList =
                    ifTrue == null ? List.of() : collectPreStatements(ifTrue);
            ifTruePreList.forEach(ifTruePre::addCStatement);
            ifTruePre.setPostStatements(new CNullStatement(parseContext));
            ifTruePre.setPreStatements(new CNullStatement(parseContext));
            CCompound ifFalsePre = new CCompound(parseContext);
            List<CStatement> ifFalsePreList = collectPreStatements(ifFalse);
            ifFalsePreList.forEach(ifFalsePre::addCStatement);
            ifFalsePre.setPostStatements(new CNullStatement(parseContext));
            ifFalsePre.setPreStatements(new CNullStatement(parseContext));

            CCompound ifTruePost = new CCompound(parseContext);
            List<CStatement> ifTruePostList =
                    ifTrue == null ? List.of() : collectPostStatements(ifTrue);
            ifTruePostList.forEach(ifTruePost::addCStatement);
            ifTruePost.setPostStatements(new CNullStatement(parseContext));
            ifTruePost.setPreStatements(new CNullStatement(parseContext));
            CCompound ifFalsePost = new CCompound(parseContext);
            List<CStatement> ifFalsePostList = collectPostStatements(ifFalse);
            ifFalsePostList.forEach(ifFalsePost::addCStatement);
            ifFalsePost.setPostStatements(new CNullStatement(parseContext));
            ifFalsePost.setPreStatements(new CNullStatement(parseContext));

            if (!ifTruePreList.isEmpty() || !ifFalsePreList.isEmpty()) {
                CIf preIf = new CIf(guardCompound, ifTruePre, ifFalsePre, parseContext);
                recordMetadata(ctx, preIf);
                preStatements.addCStatement(preIf);
            }
            if (!ifTruePostList.isEmpty() || !ifFalsePostList.isEmpty()) {
                CIf postIf = new CIf(guardCompound, ifTruePost, ifFalsePost, parseContext);
                recordMetadata(ctx, postIf);
                postStatements.addCStatement(postIf);
            }

            CComplexType smallestCommonType =
                    CComplexType.getSmallestCommonType(
                            List.of(
                                    CComplexType.getType(lhs, parseContext),
                                    CComplexType.getType(rhs, parseContext)),
                            parseContext);
            IteExpr<?> ite =
                    Ite(
                            AbstractExprs.Neq(
                                    CComplexType.getType(expr, parseContext).getNullValue(), expr),
                            smallestCommonType.castTo(lhs),
                            smallestCommonType.castTo(rhs));
            parseContext.getMetadata().create(ite, "cType", smallestCommonType);
            iteExpr = ite;
        } else {
            iteExpr = ctx.logicalOrExpression().accept(expressionVisitor);
        }

        CExpr cexpr = new CExpr(iteExpr, parseContext);
        compound.addCStatement(cexpr);
        preStatements.insertCStatementsToFront(expressionVisitor.getPreStatements());
        compound.setPreStatements(preStatements);
        recordMetadata(ctx, compound);
        compound.setPostStatements(postStatements);
        expressionVisitor.getPostStatements().forEach(postStatements::addCStatement);
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitForDeclaration(CParser.ForDeclarationContext ctx) {
        List<CDeclaration> declarations =
                declarationVisitor.getDeclarations(
                        ctx.declarationSpecifiers(), ctx.initDeclaratorList());
        CCompound compound = new CCompound(parseContext);
        for (CDeclaration declaration : declarations) {
            createVars(declaration);
            checkState(
                    declaration.getVarDecls().size() == 1,
                    "For loops cannot have struct declarations! (not yet implemented)");
            CAssignment cAssignment =
                    new CAssignment(
                            declaration.getVarDecls().get(0).getRef(),
                            declaration.getInitExpr(),
                            "=",
                            parseContext);
            recordMetadata(ctx, cAssignment);
            if (declaration.getInitExpr() != null) compound.addCStatement(cAssignment);
        }
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitForExpression(CParser.ForExpressionContext ctx) {
        CCompound compound = new CCompound(parseContext);
        for (CParser.AssignmentExpressionContext assignmentExpressionContext :
                ctx.assignmentExpression()) {
            compound.addCStatement(assignmentExpressionContext.accept(this));
        }
        recordMetadata(ctx, compound);
        return compound;
    }
}
