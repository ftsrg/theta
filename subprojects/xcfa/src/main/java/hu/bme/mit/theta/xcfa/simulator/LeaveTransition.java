package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

/**
 * Transition for leaving a call.
 *
 * A transition instance should be independent of ExplStates.
 * TODO decouple from ExplState (extend StmtExecutorInterface instead, and rename to TransitionExecutorInterface :) )
 */
public class LeaveTransition extends ProcessTransition {

	public LeaveTransition(XCFA.Process p) {
		super(p);
	}

	@Override
	public void step(ExplState state) {
		state.getProcessState(process).getCallStackPeek().end();
	}

	@Override
	public boolean enabled(ExplState state) {
		return true;
	}
}
