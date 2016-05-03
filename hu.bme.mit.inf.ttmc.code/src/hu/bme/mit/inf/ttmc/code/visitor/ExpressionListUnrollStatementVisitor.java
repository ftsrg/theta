package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.StatementAstTransformerVisitor.StatementListAst;

public class ExpressionListUnrollStatementVisitor extends StatementAstTransformerVisitor implements ExpressionVisitor<ExpressionAst>
{

	private Stack< List<ExpressionAst> > exprStack = new Stack<>();
	
	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		ExpressionAst expr = ast.getExpression();

		this.exprStack.add(new ArrayList<ExpressionAst>());
		expr = expr.accept(this);
		
		List<StatementAst> stmts = new ArrayList<>();
		List<ExpressionAst> expressions = this.exprStack.lastElement();
		if (expressions.size() == 0) {
			return new ExpressionStatementAst(expr);
		}
		
		for (ExpressionAst e : this.exprStack.lastElement()) {
			stmts.add(new ExpressionStatementAst(e));
		}
		
		this.exprStack.pop();
		
		return new StatementListAst(stmts);
		
	}
	
	@Override
	public ExpressionAst visit(ExpressionListAst ast) {
		int i = 0;
		while (i < ast.getExpressions().size()) {
			ast.getExpressions().get(i).accept(this);
			++i;
		}
		
		return ast.getExpressions().get(i - 1);
	}
	
	@Override
	public ExpressionAst visit(BinaryExpressionAst ast) {
		return new BinaryExpressionAst(ast.getLeft().accept(this), ast.getRight().accept(this), ast.getOperator());
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
		List<ExpressionAst> args = new ArrayList<>();
		for (ExpressionAst param : ast.getParams()) {
			args.add(param.accept(this));
		}		
		
		return new FunctionCallExpressionAst(ast.getName(), args);
	}

	@Override
	public ExpressionAst visit(UnaryExpressionAst ast) {		
		return new UnaryExpressionAst(ast.getOperand().accept(this), ast.getOperator());		
	}	

}
