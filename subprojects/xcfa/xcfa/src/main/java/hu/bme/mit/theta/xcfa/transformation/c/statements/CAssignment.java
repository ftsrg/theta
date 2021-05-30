package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CAssignment extends CStatement{
	private final Expr<?> lValue;
	private final CStatement rValue;

	public CAssignment(Expr<?> lValue, CStatement rValue) {
		this.lValue = lValue;
		this.rValue = rValue;
	}

	public CStatement getrValue() {
		return rValue;
	}

	public Expr<?> getlValue() {
		return lValue;
	}

	@Override
	public Expr<?> getExpression() {
		return rValue.getExpression();
	}
}
