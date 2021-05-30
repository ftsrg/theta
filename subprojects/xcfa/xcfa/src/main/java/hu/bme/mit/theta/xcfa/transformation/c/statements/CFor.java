package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;

public class CFor extends CStatement{
	private final CStatement body;
	private final Stmt init;
	private final Expr<?> guard;
	private final Stmt increment;

	public CFor(CStatement body, Stmt init, Expr<?> guard, Stmt increment) {
		this.body = body;
		this.init = init;
		this.guard = guard;
		this.increment = increment;
	}

	public Stmt getIncrement() {
		return increment;
	}

	public Expr<?> getGuard() {
		return guard;
	}

	public Stmt getInit() {
		return init;
	}

	public CStatement getBody() {
		return body;
	}
}
