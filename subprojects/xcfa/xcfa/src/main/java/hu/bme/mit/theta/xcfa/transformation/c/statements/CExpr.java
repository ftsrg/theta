package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CExpr extends CStatement{
	private final Expr<?> expr;

	public CExpr(Expr<?> expr) {
		this.expr = expr;
	}

	public Expr<?> getExpr() {
		return expr;
	}

	@Override
	public Expr<?> getExpression() {
		return expr;
	}
}
