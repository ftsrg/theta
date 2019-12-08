package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;

public interface Scheduler {
    Transition getNextTransition(Collection<Transition> enabledTransitions);
}
