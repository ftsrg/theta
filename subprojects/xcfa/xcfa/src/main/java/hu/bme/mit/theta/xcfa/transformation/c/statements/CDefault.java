package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CDefault extends CStatement{
	private final CStatement statement;

	public CDefault(CStatement statement) {
		this.statement = statement;
	}

	public CStatement getStatement() {
		return statement;
	}
}
