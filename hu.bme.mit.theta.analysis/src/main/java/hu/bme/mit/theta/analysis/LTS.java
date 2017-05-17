package hu.bme.mit.theta.analysis;

import java.util.Collection;

/**
 * Common interface for Labeled Transition Systems (LTS). An LTS can provide
 * enabled actions for a given state.
 */
@FunctionalInterface
public interface LTS<S extends State, A extends Action> {

	/**
	 * Gets the enabled actions for a given state.
	 * 
	 * @param state
	 * @return
	 */
	Collection<A> getEnabledActionsFor(S state);

}
