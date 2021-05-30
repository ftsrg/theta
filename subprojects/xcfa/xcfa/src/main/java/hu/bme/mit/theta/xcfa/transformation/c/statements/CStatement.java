package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public abstract class CStatement {
	private String id;

	public String getFunctionId() {
		return id;
	}

	public void setId(String id) {
		this.id = id;
	}

	public Expr<?> getExpression() {
		throw new RuntimeException("Cannot get expression!");
	}
}
