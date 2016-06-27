package hu.bme.mit.inf.ttmc.code.simplifier;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.AstVisitor;

public class SimplifyAstVisitor implements AstVisitor<ExpressionAst, StatementAst, DeclarationAst, DeclaratorAst, TranslationUnitAst> {

	@Override
	public ExpressionAst visit(BinaryExpressionAst ast) {
		ExpressionAst left = ast.getLeft().accept(this);
		ExpressionAst right = ast.getRight().accept(this);
		
		return ast.with(left, right);
	}

	@Override
	public ExpressionAst visit(LiteralExpressionAst ast) {
		return ast;
	}

	@Override
	public ExpressionAst visit(NameExpressionAst ast) {
		return ast;
	}

	@Override
	public ExpressionAst visit(FunctionCallExpressionAst ast) {
		List<ExpressionAst> params = ast.getParams();
		List<ExpressionAst> newParams = new ArrayList<ExpressionAst>();
		for (ExpressionAst param : params) {
			newParams.add(param.accept(this));
		}
		
		return ast.with(newParams);		
	}

	@Override
	public ExpressionAst visit(UnaryExpressionAst ast) {
		return ast.with(ast.getOperand().accept(this));
	}

	@Override
	public ExpressionAst visit(ExpressionListAst ast) {
		List<ExpressionAst> exprs = new ArrayList<ExpressionAst>();
		for (ExpressionAst expr : ast.getExpressions()) {
			exprs.add(expr.accept(this));
		}
		
		return new ExpressionListAst(exprs);
	}

	@Override
	public StatementAst visit(IfStatementAst ast) {
		return ast.with(ast.getCondition().accept(this), ast.getThen().accept(this), ast.getElse() == null ? null : ast.getElse().accept(this));
	}

	@Override
	public StatementAst visit(CompoundStatementAst ast) {
		List<StatementAst> stmts = new ArrayList<StatementAst>();
		for (StatementAst stmt : ast.getStatements()) {
			StatementAst result = stmt.accept(this);
			
			if (result instanceof StatementListAst) {
				stmts.addAll(((StatementListAst) result).getStatements());
			} else {
				stmts.add(result);
			}
		}
		
		return new CompoundStatementAst(stmts);
	}

	@Override
	public StatementAst visit(DeclarationStatementAst ast) {
		return ast.with(ast.getDeclaration().accept(this));
	}

	@Override
	public StatementAst visit(ReturnStatementAst ast) {
		return ast.with(ast.getExpression().accept(this));
	}

	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		return ast.with(ast.getExpression().accept(this));
	}

	@Override
	public StatementAst visit(WhileStatementAst ast) {
		return ast.with(ast.getCondition().accept(this), ast.getBody().accept(this));
	}

	@Override
	public StatementAst visit(ForStatementAst ast) {
		return ast.with(ast.getInit().accept(this), ast.getCondition().accept(this), ast.getIteration().accept(this), ast.getBody().accept(this));
	}

	@Override
	public StatementAst visit(DoStatementAst ast) {
		return ast.with(ast.getCondition().accept(this), ast.getBody().accept(this));
	}

	@Override
	public StatementAst visit(SwitchStatementAst ast) {
		return ast.with(ast.getExpression().accept(this), ast.getBody().accept(this));
	}

	@Override
	public StatementAst visit(CaseStatementAst ast) {
		return ast.with(ast.getExpression().accept(this));
	}

	@Override
	public StatementAst visit(DefaultStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(ContinueStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(BreakStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(GotoStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(LabeledStatementAst ast) {
		return ast.with(ast.getStatement().accept(this));
	}

	@Override
	public StatementAst visit(NullStatementAst ast) {
		return ast;
	}

	@Override
	public DeclarationAst visit(VarDeclarationAst ast) {
		List<DeclaratorAst> declarators = new ArrayList<DeclaratorAst>();
		
		for (DeclaratorAst decl : ast.getDeclarators()) {
			declarators.add(decl.accept(this));
		}
		
		return new VarDeclarationAst(ast.getSpecifier(), declarators);
	}

	@Override
	public DeclarationAst visit(FunctionDefinitionAst ast) {
		return ast.with((FunctionDeclaratorAst) ast.getDeclarator().accept(this), (CompoundStatementAst) ast.getBody().accept(this));
	}

	@Override
	public DeclaratorAst visit(InitDeclaratorAst ast) {
		return ast;
	}

	@Override
	public DeclaratorAst visit(FunctionDeclaratorAst ast) {
		return ast;
	}

	@Override
	public TranslationUnitAst visit(TranslationUnitAst ast) {
		List<DeclarationAst> decls = new ArrayList<DeclarationAst>();
		
		for (DeclarationAst decl : ast.getDeclarations()) {
			decls.add(decl.accept(this));
		}
		
		return new TranslationUnitAst(decls);
	}

}
