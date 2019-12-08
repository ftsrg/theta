package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

/**
 * Checks no deadlock.
 * Checks that it ends on final location
 * Assumes no livelock (it would get to an infinite loop)
 * Uninitialised variables only work for ints (and it assigns zero), sorry
 * <p>
 * VarIndexing is used for implementing call stack: every call digs local variables' indices one level deeper
 * <p>
 * XcfaStmtVisitor
 */
public class Simulator {

	private RuntimeState state;
	private final Scheduler s = enabledTransitions -> enabledTransitions.iterator().next();

	public Simulator(XCFA xcfa) {
		state = new RuntimeState(xcfa);
	}

	public boolean step() throws ErrorReachedException {
		return state.step(s);
	}

}
