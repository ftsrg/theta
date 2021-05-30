package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CDoWhile extends CStatement{
	private final CStatement body;
	private final Expr<?> guard;

	public CDoWhile(CStatement body, Expr<?> guard) {
		this.body = body;
		this.guard = guard;
	}

	public CStatement getBody() {
		return body;
	}

	public Expr<?> getGuard() {
		return guard;
	}
}
