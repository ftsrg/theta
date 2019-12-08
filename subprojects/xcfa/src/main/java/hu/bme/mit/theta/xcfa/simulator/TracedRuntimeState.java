package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

/**
 * A RuntimeState which notes the execution trace (to show on error)
 *
 * TODO incomplete
 */
public class TracedRuntimeState extends RuntimeState {

	/** Previous state, which should always be one transition behind the current one (as used by ExplicitChecker) */
	private RuntimeState previousState;

	/**
	 * The last transition and the previous states' transitions it should determine the trace
	 * of execution.
	 */
	private Transition lastTransition;

	public TracedRuntimeState(XCFA xcfa) {
		super(xcfa);
	}

	protected TracedRuntimeState(TracedRuntimeState toCopy) {
		super(toCopy);
		previousState = toCopy.previousState;
		lastTransition = toCopy.lastTransition;
	}

	@Override
	public TracedRuntimeState copy() {
		return new TracedRuntimeState(this);
	}
}
