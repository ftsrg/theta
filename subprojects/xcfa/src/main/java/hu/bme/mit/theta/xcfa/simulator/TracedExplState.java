package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

/**
 * A ExplState which notes down the execution trace (to show on reached error location)
 *
 * Has a reference to the previous state and transition to be able to do that.
 *
 * TODO incomplete
 */
public class TracedExplState extends ExplState {

	/** Previous state, which should always be one transition behind the current one (as used by ExplicitChecker) */
	private ExplState previousState;

	/**
	 * The last transition and the previous states' transitions it should determine the trace
	 * of execution.
	 */
	private Transition lastTransition;

	public TracedExplState(XCFA xcfa) {
		super(xcfa);
	}

	protected TracedExplState(TracedExplState toCopy) {
		super(toCopy);
		previousState = toCopy.previousState;
		lastTransition = toCopy.lastTransition;
	}

	@Override
	public TracedExplState copy() {
		return new TracedExplState(this);
	}
}
