package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;

public interface ExprTraceChecker<R extends Refutation> {
	ExprTraceStatus<R> check(final Trace<? extends ExprState, ? extends ExprAction> trace);
}
