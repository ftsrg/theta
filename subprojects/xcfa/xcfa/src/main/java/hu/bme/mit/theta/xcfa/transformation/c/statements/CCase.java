package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CCase extends CStatement{
	private final Expr<?> expr;
	private final CStatement statement;

	public CCase(Expr<?> expr, CStatement statement) {
		this.expr = expr;
		this.statement = statement;
	}

	public Expr<?> getExpr() {
		return expr;
	}

	public CStatement getStatement() {
		return statement;
	}
}
