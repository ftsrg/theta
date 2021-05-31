package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CAssignment;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CBreak;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CCase;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CCompound;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CContinue;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CDecls;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CDefault;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CDoWhile;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CExpr;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CFor;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CFunction;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CGoto;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CIf;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CProgram;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CRet;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CStatement;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CSwitch;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CWhile;
import hu.bme.mit.theta.xcfa.transformation.c.types.CType;
import org.antlr.v4.runtime.Token;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class FunctionVisitor extends CBaseVisitor<CStatement> {
	public static final FunctionVisitor instance = new FunctionVisitor();
	public static final Map<String, XcfaLocation> locLUT = new LinkedHashMap<>();

	private final Deque<Map<String, VarDecl<?>>> variables;
	private final List<VarDecl<?>> flatVariables;

	private VarDecl<?> createVar(CDeclaration declaration) {
		String name = declaration.getName();
		Map<String, VarDecl<?>> peek = variables.peek();
		//noinspection ConstantConditions
		checkState(!peek.containsKey(name), "Variable already exists!");
		peek.put(name, Var(name, Int()));
		VarDecl<?> varDecl = peek.get(name);
		flatVariables.add(varDecl);
		declaration.setVarDecl(varDecl);
		return varDecl;
	}

	public FunctionVisitor() {
		variables = new ArrayDeque<>();
		variables.push(new LinkedHashMap<>());
		flatVariables = new ArrayList<>();
	}

	@Override
	public CStatement visitCompilationUnit(CParser.CompilationUnitContext ctx) {
		ExpressionVisitor.setBitwise(ctx.accept(BitwiseChecker.instance));
		CProgram program = new CProgram();
		for (CParser.ExternalDeclarationContext externalDeclarationContext : ctx.translationUnit().externalDeclaration()) {
			CStatement accept = externalDeclarationContext.accept(this);
			if(accept instanceof CFunction) {
				program.getFunctions().add((CFunction) accept);
			}
			else if (accept instanceof CDecls) {
				program.getGlobalDeclarations().addAll(((CDecls) accept).getcDeclarations());
			}
		}
		return program;
	}

	@Override
	public CStatement visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
		System.out.print("Start: ");
		printPosInfo(ctx.getStart());
		System.out.print("Stop: ");
		printPosInfo(ctx.getStop());
		List<CDeclaration> declarations = DeclarationVisitor.instance.getDeclarations(ctx.declaration().declarationSpecifiers(), ctx.declaration().initDeclaratorList());
		CDecls decls = new CDecls();
		for (CDeclaration declaration : declarations) {
			if(declaration.getFunctionParams().size() == 0) // functions should not be interpreted as global variables
				decls.getcDeclarations().add(Tuple2.of(declaration, createVar(declaration)));
		}
		return decls;
	}

	@Override
	public CStatement visitFunctionDefinition(CParser.FunctionDefinitionContext ctx) {
		variables.push(new LinkedHashMap<>());
		locLUT.clear();
		flatVariables.clear();
		CType returnType = ctx.declarationSpecifiers().accept(TypeVisitor.instance);
		CDeclaration funcDecl = ctx.declarator().accept(DeclarationVisitor.instance);
		funcDecl.setBaseType(returnType);
		for (CDeclaration functionParam : funcDecl.getFunctionParams()) {
			if(functionParam.getName() != null) createVar(functionParam);
		}
		CParser.BlockItemListContext blockItemListContext = ctx.compoundStatement().blockItemList();
		if(blockItemListContext != null) {
			CStatement accept = blockItemListContext.accept(this);
			variables.pop();
			return new CFunction(funcDecl, accept, new ArrayList<>(flatVariables), new LinkedHashMap<>(locLUT));
		}
		variables.pop();
		return new CFunction(funcDecl, new CCompound(), new ArrayList<>(flatVariables), new LinkedHashMap<>(locLUT));
	}

	@Override
	public CStatement visitBlockItemList(CParser.BlockItemListContext ctx) {
		CCompound compound = new CCompound();
		variables.push(new LinkedHashMap<>());
		for (CParser.BlockItemContext blockItemContext : ctx.blockItem()) {
			compound.getcStatementList().add(blockItemContext.accept(this));
		}
		variables.pop();
		return compound;
	}

	@Override
	public CStatement visitIdentifierStatement(CParser.IdentifierStatementContext ctx) {
		CStatement statement = ctx.statement().accept(this);
		statement.setId(ctx.Identifier().getText());
		return statement;
	}

	@Override
	public CStatement visitCaseStatement(CParser.CaseStatementContext ctx) {
		return new CCase(
				new CExpr(ctx.constantExpression().accept(new ExpressionVisitor(variables))),
				ctx.statement().accept(this));
	}

	@Override
	public CStatement visitDefaultStatement(CParser.DefaultStatementContext ctx) {
		return new CDefault(ctx.statement().accept(this));
	}

	@Override
	public CStatement visitCompoundStatement(CParser.CompoundStatementContext ctx) {
		if(ctx.blockItemList() != null) {
			return ctx.blockItemList().accept(this);
		}
		return new CCompound();
	}

	@Override
	public CStatement visitExpressionStatement(CParser.ExpressionStatementContext ctx) {
		return ctx.expression() == null ? new CCompound() : ctx.expression().accept(this);
	}

	@Override
	public CStatement visitIfStatement(CParser.IfStatementContext ctx) {
		return new CIf(
				ctx.expression().accept(this),
				ctx.statement(0).accept(this),
				ctx.statement().size() > 1 ? ctx.statement(1).accept(this) : null);
	}

	@Override
	public CStatement visitSwitchStatement(CParser.SwitchStatementContext ctx) {
		return new CSwitch(
				ctx.expression().accept(this),
				ctx.statement().accept(this));
	}

	@Override
	public CStatement visitWhileStatement(CParser.WhileStatementContext ctx) {
		return new CWhile(
			ctx.statement().accept(this),
			ctx.expression().accept(this));
	}

	@Override
	public CStatement visitDoWhileStatement(CParser.DoWhileStatementContext ctx) {
		return new CDoWhile(
				ctx.statement().accept(this),
				ctx.expression().accept(this));
	}

	@Override
	public CStatement visitForStatement(CParser.ForStatementContext ctx) {
		return new CFor(
				ctx.statement().accept(this),
				ctx.forCondition().forInit().accept(this),
				ctx.forCondition().forTest().accept(this),
				ctx.forCondition().forIncr().accept(this));
	}

	@Override
	public CStatement visitGotoStatement(CParser.GotoStatementContext ctx) {
		return new CGoto(ctx.Identifier().getText());
	}

	@Override
	public CStatement visitContinueStatement(CParser.ContinueStatementContext ctx) {
		return new CContinue();
	}

	@Override
	public CStatement visitBreakStatement(CParser.BreakStatementContext ctx) {
		return new CBreak();
	}

	@Override
	public CStatement visitReturnStatement(CParser.ReturnStatementContext ctx) {
		return new CRet(ctx.expression() == null ? null : ctx.expression().accept(this));
	}

	@Override
	public CStatement visitStatement(CParser.StatementContext ctx) {
		return ctx.children.get(0).accept(this);
	}

	@Override
	public CStatement visitBodyDeclaration(CParser.BodyDeclarationContext ctx) {
		List<CDeclaration> declarations = DeclarationVisitor.instance.getDeclarations(ctx.declaration().declarationSpecifiers(), ctx.declaration().initDeclaratorList());
		CCompound compound = new CCompound();
		for (CDeclaration declaration : declarations) {
			if(declaration.getInitExpr() != null) compound.getcStatementList().add(new CAssignment(createVar(declaration).getRef(), declaration.getInitExpr()));
			else createVar(declaration);
		}
		return compound;
	}

	@Override
	public CStatement visitExpression(CParser.ExpressionContext ctx) {
		CCompound compound = new CCompound();
		for (CParser.AssignmentExpressionContext assignmentExpressionContext : ctx.assignmentExpression()) {
			compound.getcStatementList().add(assignmentExpressionContext.accept(this));
		}
		return compound;
	}

	@Override
	public CStatement visitAssignmentExpressionAssignmentExpression(CParser.AssignmentExpressionAssignmentExpressionContext ctx) {
		ExpressionVisitor expressionVisitor = new ExpressionVisitor(variables);
		CCompound compound = new CCompound();
		Expr<?> ret = ctx.unaryExpression().accept(expressionVisitor);
		compound.getcStatementList().addAll(expressionVisitor.getPreStatements());
		compound.getcStatementList().add(new CAssignment(ret, ctx.assignmentExpression().accept(this)));
		compound.getcStatementList().addAll(expressionVisitor.getPostStatements());
		return compound;
	}

	@Override
	public CStatement visitAssignmentExpressionConditionalExpression(CParser.AssignmentExpressionConditionalExpressionContext ctx) {
		ExpressionVisitor expressionVisitor = new ExpressionVisitor(variables);
		CCompound compound = new CCompound();
		Expr<?> ret = ctx.conditionalExpression().accept(expressionVisitor);
		compound.getcStatementList().addAll(expressionVisitor.getPreStatements());
		compound.getcStatementList().add(new CExpr(ret));
		compound.getcStatementList().addAll(expressionVisitor.getPostStatements());
		return compound;
	}

	@Override
	public CStatement visitAssignmentExpressionDigitSequence(CParser.AssignmentExpressionDigitSequenceContext ctx) {
		return new CExpr(IntLitExpr.of(BigInteger.valueOf(Long.parseLong(ctx.DigitSequence().getText()))));
	}

	@Override
	public CStatement visitForDeclaration(CParser.ForDeclarationContext ctx) {
		List<CDeclaration> declarations = DeclarationVisitor.instance.getDeclarations(ctx.declarationSpecifiers(), ctx.initDeclaratorList());
		CCompound compound = new CCompound();
		for (CDeclaration declaration : declarations) {
			if(declaration.getInitExpr() != null) compound.getcStatementList().add(new CAssignment(createVar(declaration).getRef(), declaration.getInitExpr()));
		}
		return compound;
	}

	@Override
	public CStatement visitForExpression(CParser.ForExpressionContext ctx) {
		CCompound compound = new CCompound();
		for (CParser.AssignmentExpressionContext assignmentExpressionContext : ctx.assignmentExpression()) {
			compound.getcStatementList().add(assignmentExpressionContext.accept(this));
		}
		return compound;
	}

	private void printPosInfo(Token symbol) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("startIndex: ").append(symbol.getStartIndex()).append(", ");
		stringBuilder.append("stopIndex: ").append(symbol.getStopIndex()).append(", ");
		stringBuilder.append("line: ").append(symbol.getLine()).append(", ");
		stringBuilder.append("column: ").append(symbol.getCharPositionInLine());
		System.out.println(stringBuilder);
	}
}
