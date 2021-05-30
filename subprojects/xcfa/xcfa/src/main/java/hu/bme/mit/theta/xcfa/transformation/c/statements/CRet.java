package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CRet extends CStatement{
	private final CStatement expr;

	public CRet(CStatement expr) {
		this.expr = expr;
	}

	public CStatement getExpr() {
		return expr;
	}
}
