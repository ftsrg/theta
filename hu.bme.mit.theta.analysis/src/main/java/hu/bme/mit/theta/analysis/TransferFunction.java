package hu.bme.mit.theta.analysis;

import java.util.Collection;

/**
 * Common interface for transfer functions.
 */
@FunctionalInterface
public interface TransferFunction<S extends State, A extends Action, P extends Prec> {
	/**
	 * Gets successor states of a state with a given action and precision.
	 * 
	 * @param state
	 * @param action
	 * @param prec
	 * @return Collection of successor states
	 */
	Collection<? extends S> getSuccStates(S state, A action, P prec);

}