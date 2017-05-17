package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;

/**
 * Common interface for the abstractor component. It can create an initial ARG
 * and check an ARG with a given precision.
 */
public interface Abstractor<S extends State, A extends Action, P extends Prec> {

	/**
	 * Create initial ARG.
	 *
	 * @return
	 */
	ARG<S, A> createArg();

	/**
	 * Check ARG with given precision.
	 * 
	 * @param arg
	 * @param prec
	 * @return
	 */
	AbstractorResult check(ARG<S, A> arg, P prec);

}
