package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.StatementVisitor;

public class ExpressionStatementAst extends StatementAst {

	private ExpressionAst expr;

	public ExpressionStatementAst(ExpressionAst expr) {
		this.expr = expr;
	}

	public ExpressionStatementAst with(ExpressionAst expr) {
		if (expr == this.expr)
			return this;

		return new ExpressionStatementAst(expr);
	}

	public ExpressionAst getExpression() {
		return this.expr;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.expr };
	}

	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public ExpressionStatementAst copy() {
		return new ExpressionStatementAst(expr.copy());
	}

}
