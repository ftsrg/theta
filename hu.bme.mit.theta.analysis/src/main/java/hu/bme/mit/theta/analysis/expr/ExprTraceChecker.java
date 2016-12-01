package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.Trace;

public interface ExprTraceChecker<R extends Refutation> {
	ExprTraceStatus<R> check(final Trace<? extends ExprState, ? extends ExprAction> trace);
}
