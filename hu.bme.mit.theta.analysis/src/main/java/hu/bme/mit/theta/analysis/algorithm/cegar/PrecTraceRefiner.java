package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PrecTrace;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.Refutation;

public interface PrecTraceRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation> {
	PrecTrace<S, A, P> refine(PrecTrace<S, A, P> trace, R refutation);
}
