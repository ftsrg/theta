package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

/**
 * Checks for deadlock.
 * Checks that program ends on final location
 * Assumes no livelock (it would get to an infinite loop)
 * Currently uninitialised variables only work for integers (and it assigns zero), sorry (due to ExplState)
 *
 * Uses a simple scheduler by default.
 */
public class Simulator {

	private final ExplState state;
	private final Scheduler s;

	public Simulator(XCFA xcfa) {
		s = enabledTransitions -> enabledTransitions.iterator().next();
		state = new ExplState(xcfa);
	}

	public Simulator(XCFA xcfa, Scheduler sched) {
		s = sched;
		state = new ExplState(xcfa);
	}

	public ExplState.StateSafety step() {
		state.step(s);
		return state.getSafety();
	}

}
