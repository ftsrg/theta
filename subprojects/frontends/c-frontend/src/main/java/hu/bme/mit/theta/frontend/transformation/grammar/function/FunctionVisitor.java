/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
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
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType;
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
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Struct;
import java.util.*;
import java.util.stream.Stream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

/**
 * FunctionVisitor is responsible for the instantiation of high-level model elements, such as
 * Programs, Functions, and Statements. It employs a TypeVisitor instance to provide type
 * information, a DeclarationVisitor instance to provide information on declarations (both global
 * and local, complete with initializations) and an ExpressionVisitor instance to provide
 * information on Expressions in the source code.
 */
public class FunctionVisitor extends CBaseVisitor<CStatement> {
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
        createVars(name, declaration, declaration.getActualType());
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
        if (declaration.getType().isAtomic()) {
            atomicVariables.add(varDecl);
        }
        parseContext.getMetadata().create(varDecl.getRef(), "cType", type);
        parseContext.getMetadata().create(varDecl.getName(), "cName", name);
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
    }

    @Override
    public CStatement visitCompilationUnit(CParser.CompilationUnitContext ctx) {
        variables.clear();
        atomicVariables.clear();
        variables.push(Tuple2.of("", new LinkedHashMap<>()));
        flatVariables.clear();
        functions.clear();

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
            for (VarDecl<?> varDecl : funcDecl.getVarDecls()) {
                functions.put(varDecl, funcDecl);
            }
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
        CIf cIf =
                new CIf(
                        ctx.expression().accept(this),
                        ctx.statement(0).accept(this),
                        ctx.statement().size() > 1 ? ctx.statement(1).accept(this) : null,
                        parseContext);
        recordMetadata(ctx, cIf);
        variables.pop();
        return cIf;
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
        final var ret = ctx.children.get(0).accept(this);
        currentStatementContext.pop();
        return ret;
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
            if (declaration.getActualType()
                    instanceof CArray cArray) { // we transform it into a malloc
                final var malloc =
                        new CCall("malloc", List.of(cArray.getArrayDimension()), parseContext);
                preCompound.addCStatement(malloc);
                final var free =
                        new CCall(
                                "free",
                                List.of(new CExpr(malloc.getRet().getRef(), parseContext)),
                                parseContext);
                preCompound.addCStatement(malloc);
                CAssignment cAssignment =
                        new CAssignment(
                                declaration.getVarDecls().get(0).getRef(),
                                new CExpr(malloc.getRet().getRef(), parseContext),
                                "=",
                                parseContext);
                recordMetadata(ctx, cAssignment);
                compound.addCStatement(cAssignment);
                if (!currentStatementContext.isEmpty()) {
                    final var scope = currentStatementContext.peek().get2();
                    if (scope.isPresent() && scope.get().getPostStatements() instanceof CCompound) {
                        if (scope.get().getPostStatements() == null) {
                            scope.get().setPostStatements(new CNullStatement(parseContext));
                        }
                        ((CCompound) scope.get().getPostStatements()).addCStatement(free);
                    }
                }
            }
            if (declaration.getInitExpr() != null) {
                if (declaration.getType() instanceof Struct) {
                    checkState(
                            declaration.getInitExpr() instanceof CInitializerList,
                            "Struct can only be initialized via an initializer list!");
                    final var initializerList = (CInitializerList) declaration.getInitExpr();
                    List<VarDecl<?>> varDecls = declaration.getVarDecls();
                    VarDecl<?> varDecl = varDecls.get(0);
                    final var ptrType = CComplexType.getUnsignedLong(parseContext);
                    LitExpr<?> currentValue = ptrType.getNullValue();
                    LitExpr<?> unitValue = ptrType.getUnitValue();
                    for (Tuple2<Optional<CStatement>, CStatement> statement :
                            initializerList.getStatements()) {
                        final var expr = statement.get2().getExpression();
                        final var deref =
                                Exprs.Dereference(
                                        cast(varDecl.getRef(), currentValue.getType()),
                                        cast(currentValue, currentValue.getType()),
                                        expr.getType());
                        CAssignment cAssignment =
                                new CAssignment(deref, statement.get2(), "=", parseContext);
                        recordMetadata(ctx, cAssignment);
                        compound.addCStatement(cAssignment);
                        currentValue =
                                Add(currentValue, unitValue).eval(ImmutableValuation.empty());
                    }
                } else {
                    checkState(
                            declaration.getVarDecls().size() == 1,
                            "non-struct declarations shall only have one variable!");
                    if (declaration.getInitExpr() instanceof CInitializerList initializerList) {
                        final var ptrType = CComplexType.getUnsignedLong(parseContext);
                        LitExpr<?> currentValue = ptrType.getNullValue();
                        LitExpr<?> unitValue = ptrType.getUnitValue();
                        for (Tuple2<Optional<CStatement>, CStatement> statement :
                                initializerList.getStatements()) {
                            //                            checkState(false, "Code here seems to be
                            // buggy");
                            final var expr = statement.get2().getExpression();
                            final var deref =
                                    Exprs.Dereference(
                                            cast(
                                                    declaration.getVarDecls().get(0).getRef(),
                                                    currentValue.getType()),
                                            cast(currentValue, currentValue.getType()),
                                            expr.getType());
                            CAssignment cAssignment =
                                    new CAssignment(deref, statement.get2(), "=", parseContext);
                            recordMetadata(ctx, cAssignment);
                            compound.addCStatement(cAssignment);
                            currentValue =
                                    Add(currentValue, unitValue).eval(ImmutableValuation.empty());
                        }
                    } else {
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
                }
            } else {
                // if there is no initializer, then we'll add an assumption regarding min and max
                // values
                if (declaration.getType() instanceof Struct) {
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
            CStatement ifTrue = ctx.ifTrue.accept(this);
            CStatement ifFalse = ctx.ifFalse.accept(this);

            Expr<?> expr = ctx.logicalOrExpression().accept(expressionVisitor);
            Expr<?> lhs = ifTrue.getExpression();
            Expr<?> rhs = ifFalse.getExpression();

            CCompound guardCompound = new CCompound(parseContext);
            guardCompound.addCStatement(new CExpr(expr, parseContext));
            guardCompound.setPostStatements(new CNullStatement(parseContext));
            guardCompound.setPreStatements(new CNullStatement(parseContext));

            CCompound ifTruePre = new CCompound(parseContext);
            List<CStatement> ifTruePreList = collectPreStatements(ifTrue);
            ifTruePreList.forEach(ifTruePre::addCStatement);
            ifTruePre.setPostStatements(new CNullStatement(parseContext));
            ifTruePre.setPreStatements(new CNullStatement(parseContext));
            CCompound ifFalsePre = new CCompound(parseContext);
            List<CStatement> ifFalsePreList = collectPreStatements(ifFalse);
            ifFalsePreList.forEach(ifFalsePre::addCStatement);
            ifFalsePre.setPostStatements(new CNullStatement(parseContext));
            ifFalsePre.setPreStatements(new CNullStatement(parseContext));

            CCompound ifTruePost = new CCompound(parseContext);
            List<CStatement> ifTruePostList = collectPostStatements(ifTrue);
            ifTruePostList.forEach(ifTruePost::addCStatement);
            ifTruePost.setPostStatements(new CNullStatement(parseContext));
            ifTruePost.setPreStatements(new CNullStatement(parseContext));
            CCompound ifFalsePost = new CCompound(parseContext);
            List<CStatement> ifFalsePostList = collectPostStatements(ifFalse);
            ifFalsePostList.forEach(ifFalsePost::addCStatement);
            ifFalsePost.setPostStatements(new CNullStatement(parseContext));
            ifFalsePost.setPreStatements(new CNullStatement(parseContext));

            if (!ifTruePreList.isEmpty() || !ifFalsePreList.isEmpty()) {
                preStatements.addCStatement(
                        new CIf(guardCompound, ifTruePre, ifFalsePre, parseContext));
            }
            if (!ifTruePostList.isEmpty() || !ifFalsePostList.isEmpty()) {
                postStatements.addCStatement(
                        new CIf(guardCompound, ifTruePost, ifFalsePost, parseContext));
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
