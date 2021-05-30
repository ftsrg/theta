package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CSwitch extends CStatement{
	private final CStatement testValue;
	private final CStatement body;

	public CSwitch(CStatement testValue, CStatement body) {
		this.testValue = testValue;
		this.body = body;
	}

	public CStatement getBody() {
		return body;
	}

	public CStatement getTestValue() {
		return testValue;
	}
}
