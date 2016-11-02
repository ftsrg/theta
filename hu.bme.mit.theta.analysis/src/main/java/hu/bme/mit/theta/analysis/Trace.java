package hu.bme.mit.theta.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

/**
 * Represents a trace in the form of a (State, Action, State, ..., State,
 * Action, State) sequence. A trace always contains at least one state and the
 * number of actions is one less than the number of states.
 */
public final class Trace<S extends State, A extends Action> {

	private final List<S> states;
	private final List<A> actions;

	private Trace(final List<? extends S> states, final List<? extends A> actions) {
		checkNotNull(states);
		checkNotNull(actions);
		checkArgument(states.size() > 0, "A trace must contain at least one state.");
		checkArgument(states.size() == actions.size() + 1, "#states = #actions + 1 must hold.");
		this.states = ImmutableList.copyOf(states);
		this.actions = ImmutableList.copyOf(actions);
	}

	/**
	 * Create a trace. The size of states must be at least one, and the size of
	 * the actions must be one less than the number of states.
	 */
	public static <S extends State, A extends Action> Trace<S, A> create(final List<? extends S> states,
			final List<? extends A> actions) {
		return new Trace<>(states, actions);
	}

	/**
	 * Gets the length of the trace, which is the number of states.
	 */
	public int length() {
		return states.size();
	}

	public S getState(final int i) {
		checkElementIndex(0, states.size());
		return states.get(i);
	}

	public A getAction(final int i) {
		checkElementIndex(0, actions.size());
		return actions.get(i);
	}

	public List<S> getStates() {
		return states;
	}

	public List<A> getActions() {
		return actions;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Trace(");
		for (int i = 0; i < length(); ++i) {
			sb.append(getState(i));
			if (i < length() - 1) {
				sb.append(" ---[");
				sb.append(getAction(i));
				sb.append("]--> ");
			}
		}
		sb.append(")");
		return sb.toString();
	}
}
