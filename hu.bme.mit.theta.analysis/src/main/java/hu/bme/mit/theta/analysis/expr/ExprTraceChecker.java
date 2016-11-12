package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.Trace;

public interface ExprTraceChecker<R extends Refutation> {
	ExprTraceStatus2<R> check(final Trace<? extends ExprState, ? extends ExprAction> trace,
			final ExprStatePredicate init, final ExprStatePredicate target);
}
