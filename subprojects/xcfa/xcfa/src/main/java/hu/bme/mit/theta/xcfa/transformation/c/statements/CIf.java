package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CIf extends CStatement{
	private final Expr<?> guard;
	private final CStatement body;
	private final CStatement elseStatement;

	public CIf(Expr<?> guard, CStatement body, CStatement elseStatement) {
		this.guard = guard;
		this.body = body;
		this.elseStatement = elseStatement;
	}

	public CStatement getElseStatement() {
		return elseStatement;
	}

	public CStatement getBody() {
		return body;
	}

	public Expr<?> getGuard() {
		return guard;
	}
}
