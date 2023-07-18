/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.ExpressionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseChecker;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseOption;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.GlobalDeclUsageVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssignment;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssume;
import hu.bme.mit.theta.frontend.transformation.model.statements.CBreak;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCase;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCompound;
import hu.bme.mit.theta.frontend.transformation.model.statements.CContinue;
import hu.bme.mit.theta.frontend.transformation.model.statements.CDecls;
import hu.bme.mit.theta.frontend.transformation.model.statements.CDefault;
import hu.bme.mit.theta.frontend.transformation.model.statements.CDoWhile;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CFor;
import hu.bme.mit.theta.frontend.transformation.model.statements.CFunction;
import hu.bme.mit.theta.frontend.transformation.model.statements.CGoto;
import hu.bme.mit.theta.frontend.transformation.model.statements.CIf;
import hu.bme.mit.theta.frontend.transformation.model.statements.CInitializerList;
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram;
import hu.bme.mit.theta.frontend.transformation.model.statements.CRet;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.statements.CSwitch;
import hu.bme.mit.theta.frontend.transformation.model.statements.CWhile;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Struct;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.StringJoiner;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.grammar.UtilsKt.textWithWS;

/**
 * FunctionVisitor is responsible for the instantiation of high-level model elements, such as Programs, Functions,
 * and Statements. It employs a TypeVisitor instance to provide type information, a DeclarationVisitor instance to
 * provide information on declarations (both global and local, complete with initializations) and an ExpressionVisitor
 * instance to provide information on Expressions in the source code.
 */
public class FunctionVisitor extends CBaseVisitor<CStatement> {
    private final ParseContext parseContext;
    private final DeclarationVisitor declarationVisitor;
    private final GlobalDeclUsageVisitor globalDeclUsageVisitor;
    private final TypeVisitor typeVisitor;
    private final TypedefVisitor typedefVisitor;

    public void clear() {
        variables.clear();
        flatVariables.clear();
        functions.clear();
    }

    private final Deque<Tuple2<String, Map<String, VarDecl<?>>>> variables;
    private int anonCnt = 0;
    private final List<VarDecl<?>> flatVariables;
    private final Map<VarDecl<?>, CDeclaration> functions;

    private Collection<VarDecl<?>> createVars(CDeclaration declaration) {
        String name = declaration.getName();
        List<VarDecl<?>> vars = new ArrayList<>();
        createVars(name, declaration, declaration.getActualType(), vars);
        return vars;
    }

    private String getName(final String name) {
        final StringJoiner sj = new StringJoiner("::");
        for (Iterator<Tuple2<String, Map<String, VarDecl<?>>>> iterator = variables.descendingIterator(); iterator.hasNext(); ) {
            Tuple2<String, Map<String, VarDecl<?>>> variable = iterator.next();
            if (!variable.get1().equals(""))
                sj.add(variable.get1());
        }
        sj.add(name);
        return sj.toString();
    }

    private void createVars(String name, CDeclaration declaration, CComplexType type, List<VarDecl<?>> vars) {
        if (type instanceof CStruct) {
            ((CStruct) type).getFields().forEach((s, type1) -> {
                createVars(name + "." + s, declaration, type1, vars);
            });
        }
        Tuple2<String, Map<String, VarDecl<?>>> peek = variables.peek();
        VarDecl<?> varDecl = Var(getName(name), type.getSmtType());
        if (peek.get2().containsKey(name)) {
            System.err.println("WARNING: Variable already exists: " + name);
            varDecl = peek.get2().get(name);
        }
        peek.get2().put(name, varDecl);
        flatVariables.add(varDecl);
        parseContext.getMetadata().create(varDecl.getRef(), "cType", type);
        parseContext.getMetadata().create(varDecl.getName(), "cName", name);
        declaration.addVarDecl(varDecl);
    }

    public FunctionVisitor(final ParseContext parseContext) {
        this.declarationVisitor = new DeclarationVisitor(parseContext, this);
        this.typedefVisitor = declarationVisitor.getTypedefVisitor();
        this.typeVisitor = declarationVisitor.getTypeVisitor();
        variables = new ArrayDeque<>();
        variables.push(Tuple2.of("", new LinkedHashMap<>()));
        flatVariables = new ArrayList<>();
        functions = new LinkedHashMap<>();
        this.parseContext = parseContext;
        globalDeclUsageVisitor = new GlobalDeclUsageVisitor(declarationVisitor);
    }

    @Override
    public CStatement visitCompilationUnit(CParser.CompilationUnitContext ctx) {
        variables.clear();
        variables.push(Tuple2.of("", new LinkedHashMap<>()));
        flatVariables.clear();
        functions.clear();

        ctx.accept(typedefVisitor);
        // ExpressionVisitor.setBitwise(ctx.accept(BitwiseChecker.instance));

        List<CParser.ExternalDeclarationContext> globalUsages = globalDeclUsageVisitor.getGlobalUsages(ctx);

        // if arithemetic is set on efficient, we change it to either bv or int arithmetic here
        if (parseContext.getArithmetic() == ArchitectureConfig.ArithmeticType.efficient) { // if it wasn't on efficient, the check returns manual
            BitwiseOption bitwiseOption = BitwiseChecker.checkIfBitwise(parseContext, globalUsages);
            parseContext.setArithmetic((bitwiseOption == BitwiseOption.INTEGER) ? ArchitectureConfig.ArithmeticType.integer : ArchitectureConfig.ArithmeticType.bitvector);
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

    public void recordMetadata(ParserRuleContext ctx, CStatement statement) {
        Token start = ctx.getStart();
        Token stop = ctx.getStop();
        String stopText = stop.getText();
        String[] stopTextLines = stopText.split("\r\n|\r|\n", -1);
        int stopLines = stopTextLines.length - 1;
        int lineNumberStart = start.getLine();
        int colNumberStart = start.getCharPositionInLine();
        int lineNumberStop = stop.getLine() + stopLines;
        int colNumberStop = stopLines == 0 ? stop.getCharPositionInLine() + stopText.length() - 1 : stopTextLines[stopLines].length();
        int offsetStart = start.getStartIndex();
        int offsetEnd = stop.getStopIndex();
        statement.setLineNumberStart(lineNumberStart);
        statement.setLineNumberStop(lineNumberStop);
        statement.setColNumberStart(colNumberStart);
        statement.setColNumberStop(colNumberStop);
        statement.setOffsetStart(offsetStart);
        statement.setOffsetEnd(offsetEnd);
        statement.setSourceText(textWithWS(ctx));
    }


    @Override
    public CStatement visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
        List<CDeclaration> declarations = declarationVisitor.getDeclarations(ctx.declaration().declarationSpecifiers(), ctx.declaration().initDeclaratorList());
        CDecls decls = new CDecls(parseContext);
        for (CDeclaration declaration : declarations) {
            if (!declaration.getType().isTypedef()) {
                if (!declaration.isFunc()) { // functions should not be interpreted as global variables
                    createVars(declaration);
                    for (VarDecl<?> varDecl : declaration.getVarDecls()) {
                        decls.getcDeclarations().add(Tuple2.of(declaration, varDecl));
                    }
                } else {
                    CSimpleType returnType = declaration.getType();
                    declaration.setType(returnType);
                    if (!variables.peek().get2().containsKey(declaration.getName())) {
                        parseContext.getMetadata().create(declaration.getName(), "cType", returnType.getActualType());
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
        if (returnType.isTypedef()) return new CCompound(parseContext);
        CDeclaration funcDecl = ctx.declarator().accept(declarationVisitor);
        funcDecl.setType(returnType);
        if (!variables.peek().get2().containsKey(funcDecl.getName())) {
            parseContext.getMetadata().create(funcDecl.getName(), "cType", returnType.getActualType());
            createVars(funcDecl);
            for (VarDecl<?> varDecl : funcDecl.getVarDecls()) {
                functions.put(varDecl, funcDecl);
            }
        }
        variables.push(Tuple2.of(funcDecl.getName(), new LinkedHashMap<>()));
        flatVariables.clear();
        for (CDeclaration functionParam : funcDecl.getFunctionParams()) {
            if (functionParam.getName() != null)
                createVars(functionParam);
        }
        CParser.BlockItemListContext blockItemListContext = ctx.compoundStatement().blockItemList();
        if (blockItemListContext != null) {
            CStatement accept = blockItemListContext.accept(this);
            variables.pop();
            CFunction cFunction = new CFunction(funcDecl, accept, new ArrayList<>(flatVariables), parseContext);
            recordMetadata(ctx, cFunction);
            return cFunction;
        }
        variables.pop();
        CCompound cCompound = new CCompound(parseContext);
        CFunction cFunction = new CFunction(funcDecl, cCompound, new ArrayList<>(flatVariables), parseContext);
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
            compound.getcStatementList().add(blockItemContext.accept(this));
        }
        if (ctx.parent.parent.parent.parent instanceof CParser.BlockItemListContext)
            variables.pop();
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitIdentifierStatement(CParser.IdentifierStatementContext ctx) {
        CStatement statement = ctx.statement().accept(this);
        CCompound compound = new CCompound(parseContext);
        compound.getcStatementList().add(statement);
        compound.setId(ctx.Identifier().getText());
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitCaseStatement(CParser.CaseStatementContext ctx) {
        parseContext.getCStmtCounter().incrementBranches();
        CExpr cexpr = new CExpr(ctx.constantExpression().accept(new ExpressionVisitor(parseContext, this, variables, functions, typedefVisitor, typeVisitor)), parseContext);
        CCase cCase = new CCase(
                cexpr,
                ctx.statement().accept(this), parseContext);
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
        CStatement statement = ctx.expression() == null ? new CCompound(parseContext) : ctx.expression().accept(this);
        recordMetadata(ctx, statement);
        return statement;
    }

    @Override
    public CStatement visitIfStatement(CParser.IfStatementContext ctx) {
        parseContext.getCStmtCounter().incrementBranches();
        variables.push(Tuple2.of("if" + anonCnt++, new LinkedHashMap<>()));
        CIf cIf = new CIf(
                ctx.expression().accept(this),
                ctx.statement(0).accept(this),
                ctx.statement().size() > 1 ? ctx.statement(1).accept(this) : null, parseContext);
        recordMetadata(ctx, cIf);
        variables.pop();
        return cIf;
    }

    @Override
    public CStatement visitSwitchStatement(CParser.SwitchStatementContext ctx) {
        variables.push(Tuple2.of("switch" + anonCnt++, new LinkedHashMap<>()));
        CSwitch cSwitch = new CSwitch(
                ctx.expression().accept(this),
                ctx.statement().accept(this), parseContext);
        recordMetadata(ctx, cSwitch);
        variables.pop();
        return cSwitch;
    }

    @Override
    public CStatement visitWhileStatement(CParser.WhileStatementContext ctx) {
        parseContext.getCStmtCounter().incrementWhileLoops();
        variables.push(Tuple2.of("while" + anonCnt++, new LinkedHashMap<>()));
        CWhile cWhile = new CWhile(
                ctx.statement().accept(this),
                ctx.expression().accept(this), parseContext);
        recordMetadata(ctx, cWhile);
        variables.pop();
        return cWhile;
    }

    @Override
    public CStatement visitDoWhileStatement(CParser.DoWhileStatementContext ctx) {
        variables.push(Tuple2.of("dowhile" + anonCnt++, new LinkedHashMap<>()));
        CDoWhile cDoWhile = new CDoWhile(
                ctx.statement().accept(this),
                ctx.expression().accept(this), parseContext);
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
            newCCompound1.getcStatementList().add(newCCompound2);
            Expr<?> one = CComplexType.getSignedInt(parseContext).getUnitValue();
            parseContext.getMetadata().create(one, "cType", CComplexType.getSignedInt(parseContext));
            newCCompound2.getcStatementList().add(new CExpr(one, parseContext));
            newCCompound2.setPreStatements(newCCompound3);
            newCCompound2.setPostStatements(newCCompound4);
            test = newCCompound1;
            recordMetadata(ctx.forCondition(), test);
        }
        CStatement incr = ctx.forCondition().forIncr().accept(this);
        CFor cFor = new CFor(
                ctx.statement().accept(this),
                init,
                test,
                incr, parseContext);
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
        CRet cRet = new CRet(ctx.expression() == null ? null : ctx.expression().accept(this), parseContext);
        recordMetadata(ctx, cRet);
        return cRet;
    }

    @Override
    public CStatement visitStatement(CParser.StatementContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public CStatement visitBodyDeclaration(CParser.BodyDeclarationContext ctx) {
        List<CDeclaration> declarations = declarationVisitor.getDeclarations(ctx.declaration().declarationSpecifiers(), ctx.declaration().initDeclaratorList());
        CCompound compound = new CCompound(parseContext);
        for (CDeclaration declaration : declarations) {
            if (declaration.getInitExpr() != null) {
                createVars(declaration);
                if (declaration.getType() instanceof Struct) {
                    checkState(declaration.getInitExpr() instanceof CInitializerList, "Struct can only be initialized via an initializer list!");
                    List<VarDecl<?>> varDecls = declaration.getVarDecls();
                    for (int i = 0; i < varDecls.size(); i++) {
                        VarDecl<?> varDecl = varDecls.get(i);
                        Tuple2<Optional<CStatement>, CStatement> initializer = ((CInitializerList) declaration.getInitExpr()).getStatements().get(i);

                        CAssignment cAssignment = new CAssignment(varDecl.getRef(), initializer.get2(), "=", parseContext);
                        recordMetadata(ctx, cAssignment);
                        compound.getcStatementList().add(cAssignment);
                    }
                } else {
                    checkState(declaration.getVarDecls().size() == 1, "non-struct declarations shall only have one variable!");
                    CAssignment cAssignment = new CAssignment(declaration.getVarDecls().get(0).getRef(), declaration.getInitExpr(), "=", parseContext);
                    recordMetadata(ctx, cAssignment);
                    compound.getcStatementList().add(cAssignment);
                }
            } else {
                createVars(declaration);
                // if there is no initializer, then we'll add an assumption regarding min and max values
                if (declaration.getType() instanceof Struct) {
                    for (VarDecl<?> varDecl : declaration.getVarDecls()) {
                        if (!(varDecl.getType() instanceof ArrayType) && !(varDecl.getType() instanceof BoolType)) { // BoolType is either well-defined true/false, or a struct in disguise
                            AssumeStmt assumeStmt = CComplexType.getType(varDecl.getRef(), parseContext).limit(varDecl.getRef());
                            CAssume cAssume = new CAssume(assumeStmt, parseContext);
                            compound.getcStatementList().add(cAssume);
                        }
                    }
                } else {
                    VarDecl<?> varDecl = declaration.getVarDecls().get(0);
                    if (!(varDecl.getType() instanceof ArrayType) && !(varDecl.getType() instanceof BoolType)) {
                        AssumeStmt assumeStmt = CComplexType.getType(varDecl.getRef(), parseContext).limit(varDecl.getRef());
                        CAssume cAssume = new CAssume(assumeStmt, parseContext);
                        compound.getcStatementList().add(cAssume);
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
        for (CParser.AssignmentExpressionContext assignmentExpressionContext : ctx.assignmentExpression()) {
            compound.getcStatementList().add(assignmentExpressionContext.accept(this));
        }
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitAssignmentExpressionAssignmentExpression(CParser.AssignmentExpressionAssignmentExpressionContext ctx) {
        ExpressionVisitor expressionVisitor = new ExpressionVisitor(parseContext, this, variables, functions, typedefVisitor, typeVisitor);
        CCompound compound = new CCompound(parseContext);
        CCompound preStatements = new CCompound(parseContext);
        CCompound postStatements = new CCompound(parseContext);
        Expr<?> ret = ctx.unaryExpression().accept(expressionVisitor);
        CAssignment cAssignment = new CAssignment(ret, ctx.assignmentExpression().accept(this), ctx.assignmentOperator().getText(), parseContext);
        compound.getcStatementList().add(cAssignment);
        preStatements.getcStatementList().addAll(expressionVisitor.getPreStatements());
        compound.setPreStatements(preStatements);
        recordMetadata(ctx, compound);
        postStatements.getcStatementList().addAll(expressionVisitor.getPostStatements());
        compound.setPostStatements(postStatements);
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitAssignmentExpressionConditionalExpression(CParser.AssignmentExpressionConditionalExpressionContext ctx) {
        ExpressionVisitor expressionVisitor = new ExpressionVisitor(parseContext, this, variables, functions, typedefVisitor, typeVisitor);
        CCompound compound = new CCompound(parseContext);
        CCompound preStatements = new CCompound(parseContext);
        CCompound postStatements = new CCompound(parseContext);
        Expr<?> ret = ctx.conditionalExpression().accept(expressionVisitor);
        CExpr cexpr = new CExpr(ret, parseContext);
        compound.getcStatementList().add(cexpr);
        preStatements.getcStatementList().addAll(expressionVisitor.getPreStatements());
        compound.setPreStatements(preStatements);
        recordMetadata(ctx, compound);
        postStatements.getcStatementList().addAll(expressionVisitor.getPostStatements());
        compound.setPostStatements(postStatements);
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitForDeclaration(CParser.ForDeclarationContext ctx) {
        List<CDeclaration> declarations = declarationVisitor.getDeclarations(ctx.declarationSpecifiers(), ctx.initDeclaratorList());
        CCompound compound = new CCompound(parseContext);
        for (CDeclaration declaration : declarations) {
            createVars(declaration);
            checkState(declaration.getVarDecls().size() == 1, "For loops cannot have struct declarations! (not yet implemented)");
            CAssignment cAssignment = new CAssignment(declaration.getVarDecls().get(0).getRef(), declaration.getInitExpr(), "=", parseContext);
            recordMetadata(ctx, cAssignment);
            if (declaration.getInitExpr() != null) compound.getcStatementList().add(cAssignment);
        }
        recordMetadata(ctx, compound);
        return compound;
    }

    @Override
    public CStatement visitForExpression(CParser.ForExpressionContext ctx) {
        CCompound compound = new CCompound(parseContext);
        for (CParser.AssignmentExpressionContext assignmentExpressionContext : ctx.assignmentExpression()) {
            compound.getcStatementList().add(assignmentExpressionContext.accept(this));
        }
        recordMetadata(ctx, compound);
        return compound;
    }
}
