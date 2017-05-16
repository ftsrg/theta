package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

/**
 * Interface for refining a precision based on a trace and a refutation.
 */
public interface PrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation> {

	/**
	 * Refine a precision based on a trace and a refutation.
	 */
	P refine(P prec, Trace<S, A> trace, R refutation);

}
