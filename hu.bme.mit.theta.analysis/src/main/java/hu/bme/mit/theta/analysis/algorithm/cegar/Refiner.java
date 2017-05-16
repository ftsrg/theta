package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;

/**
 * Common interface for refiners. It takes an ARG and a precision, checks if the
 * counterexample in the ARG is feasible and if not, it refines the precision
 * and may also prune the ARG.
 */
public interface Refiner<S extends State, A extends Action, P extends Prec> {

	/**
	 * Checks if the counterexample in the ARG is feasible. If not, refines the
	 * precision and prunes the ARG.
	 * 
	 * @param arg
	 * @param prec
	 * @return
	 */
	RefinerResult<S, A, P> refine(ARG<S, A> arg, P prec);
}
