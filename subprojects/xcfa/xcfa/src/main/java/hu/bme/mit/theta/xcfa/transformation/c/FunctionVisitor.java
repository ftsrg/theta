package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CBreak;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CCompound;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CContinue;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CDoWhile;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CExpr;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CFor;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CGoto;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CIf;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CRet;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CStatement;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CSwitch;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CWhile;
import hu.bme.mit.theta.xcfa.transformation.c.types.CType;

import java.util.List;

public class FunctionVisitor extends CBaseVisitor<CStatement> {
	public static final FunctionVisitor instance = new FunctionVisitor();

	@Override
	public CStatement visitFunctionDefinition(CParser.FunctionDefinitionContext ctx) {
		CType returnType = ctx.declarationSpecifiers().accept(TypeVisitor.instance);
		CDeclaration funcDecl = ctx.declarator().accept(DeclarationVisitor.instance);
		CParser.BlockItemListContext blockItemListContext = ctx.compoundStatement().blockItemList();
		if(blockItemListContext != null) {
			return blockItemListContext.accept(this);
		}
		return new CCompound();
	}

	@Override
	public CStatement visitBlockItemList(CParser.BlockItemListContext ctx) {
		CCompound compound = new CCompound();
		for (CParser.BlockItemContext blockItemContext : ctx.blockItem()) {
			compound.getcStatementList().add(blockItemContext.accept(this));
		}
		return compound;
	}

	@Override
	public CStatement visitIdentifierStatement(CParser.IdentifierStatementContext ctx) {
		CStatement statement = ctx.statement().accept(this);
		statement.setId(ctx.Identifier().getText());
		return statement;
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
		return ctx.expression() == null ? new CCompound() : new CExpr(ctx.expression().accept(null)); // TODO
	}

	@Override
	public CStatement visitIfStatement(CParser.IfStatementContext ctx) {
		return new CIf(
				ctx.expression().accept(null), // TODO
				ctx.statement(0).accept(this),
				ctx.statement().size() > 1 ? ctx.statement(1).accept(this) : null);
	}

	@Override
	public CStatement visitSwitchStatement(CParser.SwitchStatementContext ctx) {
		return new CSwitch(
				ctx.expression().accept(null), // TODO
				ctx.statement().accept(this));
	}

	@Override
	public CStatement visitWhileStatement(CParser.WhileStatementContext ctx) {
		return new CWhile(
			ctx.statement().accept(this),
			ctx.expression().accept(null)); // TODO
	}

	@Override
	public CStatement visitDoWhileStatement(CParser.DoWhileStatementContext ctx) {
		return new CDoWhile(
				ctx.statement().accept(this),
				ctx.expression().accept(null)); // TODO
	}

	@Override
	public CStatement visitForStatement(CParser.ForStatementContext ctx) {
		return new CFor(
				ctx.statement().accept(this),
				ctx.forCondition().forInit().accept(null),
				ctx.forCondition().forTest().accept(null),
				ctx.forCondition().forIncr().accept(null)); // TODO
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
		return new CRet(ctx.expression() == null ? null : ctx.expression().accept(null)); // TODO
	}

	@Override
	public CStatement visitBodyDeclaration(CParser.BodyDeclarationContext ctx) {
		List<CDeclaration> declarations = DeclarationVisitor.instance.getDeclarations(ctx.declaration());
		return null;
	}
}
