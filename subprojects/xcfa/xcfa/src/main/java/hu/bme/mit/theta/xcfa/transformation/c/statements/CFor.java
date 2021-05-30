package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;

public class CFor extends CStatement{
	private final CStatement body;
	private final CStatement init;
	private final CStatement guard;
	private final CStatement increment;

	public CFor(CStatement body, CStatement init, CStatement guard, CStatement increment) {
		this.body = body;
		this.init = init;
		this.guard = guard;
		this.increment = increment;
	}

	public CStatement getIncrement() {
		return increment;
	}

	public CStatement getGuard() {
		return guard;
	}

	public CStatement getInit() {
		return init;
	}

	public CStatement getBody() {
		return body;
	}
}
