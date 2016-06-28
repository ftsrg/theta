package hu.bme.mit.inf.ttmc.code.simplifier.visitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.simplifier.SimplifyAstVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.StatementListAst;

public class ExpressionListUnrollVisitor extends SimplifyAstVisitor {
	
	private Stack< List<ExpressionAst> > exprStack = new Stack<>();
		
	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		ExpressionAst expr = ast.getExpression();

		this.exprStack.add(new ArrayList<ExpressionAst>());
		expr = expr.accept(this);
		
		List<StatementAst> stmts = new ArrayList<>();
		List<ExpressionAst> expressions = this.exprStack.lastElement();
		if (expressions.size() == 0) { // There was no expression list inside
			return ast;
		}
		
		for (ExpressionAst e : this.exprStack.lastElement()) {
			stmts.add(new ExpressionStatementAst(e));
		}
		stmts.add(new ExpressionStatementAst(expr));
		
		this.exprStack.pop();
		
		return new StatementListAst(stmts);
	}
	
	@Override
	public ExpressionAst visit(ExpressionListAst ast) {
		ExpressionAst last = ast.getExpressions().get(0);
		
		for (ExpressionAst expr : ast.getExpressions()) {
			last = expr.accept(this);
			this.exprStack.lastElement().add(last);
		}
		
		return last;
	}
}
