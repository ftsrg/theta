package hu.bme.mit.theta.xcfa.simulator;

import java.util.Collection;

/**
 * Scheduler selects a transition from enabled transition.
 * Used by simulator.
 */
public interface Scheduler {
	Transition getNextTransition(Collection<Transition> enabledTransitions);
}
