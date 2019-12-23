package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A ExplState which notes down the execution trace (to show on reached error location)
 *
 * Has a reference to the previous state and transition to be able to do that.
 *
 */
public class TracedExplState extends ExplState {

	/** Previous state, which should always be one transition behind the current one (as used by ExplicitChecker) */
	private TracedExplState previousState;

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
	public List<Transition> getTrace() {
		List<Transition> transitions = new ArrayList<>();
		TracedExplState p = this;
		while (p.lastTransition != null) {
			transitions.add(p.lastTransition);
			p = p.previousState;
		}
		Collections.reverse(transitions);
		return transitions;
	}

	@Override
	public TracedExplState copy() {
		return new TracedExplState(this);
	}

	@Override
	public ExplState executeTransition(Transition transition) {
		TracedExplState newState = copy();
		transition.execute(newState);
		newState.lastTransition = transition;
		newState.previousState = this;
		return newState;
	}
}
