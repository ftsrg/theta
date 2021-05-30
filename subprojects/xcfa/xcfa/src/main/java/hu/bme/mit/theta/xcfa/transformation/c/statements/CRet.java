package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CRet extends CStatement{
	private final Expr<?> expr;

	public CRet(Expr<?> expr) {
		this.expr = expr;
	}

	public Expr<?> getExpr() {
		return expr;
	}
}
