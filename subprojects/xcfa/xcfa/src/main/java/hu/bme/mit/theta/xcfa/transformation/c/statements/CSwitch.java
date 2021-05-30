package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CSwitch extends CStatement{
	private final Expr<?> testValue;
	private final CStatement body;

	public CSwitch(Expr<?> testValue, CStatement body) {
		this.testValue = testValue;
		this.body = body;
	}

	public CStatement getBody() {
		return body;
	}

	public Expr<?> getTestValue() {
		return testValue;
	}
}
