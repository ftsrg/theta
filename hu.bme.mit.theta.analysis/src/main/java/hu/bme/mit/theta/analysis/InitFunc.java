package hu.bme.mit.theta.analysis;

import java.util.Collection;

/**
 * Common interface for initial functions.
 */
@FunctionalInterface
public interface InitFunc<S extends State, P extends Prec> {

	/**
	 * Gets the initial states with a given precision.
	 * 
	 * @param prec
	 * @return Collection of initial states
	 */
	Collection<? extends S> getInitStates(P prec);

}
