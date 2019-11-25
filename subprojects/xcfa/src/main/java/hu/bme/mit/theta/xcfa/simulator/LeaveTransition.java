package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

public class LeaveTransition extends ProcessTransition {

	public LeaveTransition(XCFA.Process p) {
		super(p);
	}

	@Override
	public void step(RuntimeState state) {
		state.getProcessState(process).getCallStackPeek().end();
	}

	@Override
	public boolean enabled(RuntimeState state) {
		return true;
	}
}
