package hu.bme.mit.theta.xcfa.simulator;

import java.util.Collection;

public interface Scheduler {
	Transition getNextTransition(Collection<Transition> enabledTransitions);
}
