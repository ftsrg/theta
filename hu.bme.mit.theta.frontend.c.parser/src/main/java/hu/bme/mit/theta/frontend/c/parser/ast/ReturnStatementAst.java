package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.StatementVisitor;

public class ReturnStatementAst extends StatementAst {

	private ExpressionAst expr;

	public ReturnStatementAst(ExpressionAst expr) {
		this.expr = expr;
	}

	public ReturnStatementAst with(ExpressionAst expr) {
		if (expr == this.expr)
			return this;

		return new ReturnStatementAst(expr);
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
	public ReturnStatementAst copy() {
		return new ReturnStatementAst(expr.copy());
	}

}
