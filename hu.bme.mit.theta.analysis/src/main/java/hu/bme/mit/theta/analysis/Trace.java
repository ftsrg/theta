package hu.bme.mit.theta.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

/**
 * Represents an immutable, alternating trace in the form of a (State, Action,
 * State, ..., State, Action, State) sequence. A trace always contains at least
 * one state and the number of actions is one less than the number of states.
 */
public final class Trace<S, A> {

	private final ImmutableList<S> states;
	private final ImmutableList<A> actions;

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
	public static <S, A> Trace<S, A> of(final List<? extends S> states, final List<? extends A> actions) {
		return new Trace<>(states, actions);
	}

	/**
	 * Gets the length of the trace, which is the number of actions.
	 */
	public int length() {
		return actions.size();
	}

	/**
	 * Gets a state at a given index.
	 *
	 * @param i Index
	 * @return State
	 */
	public S getState(final int i) {
		checkElementIndex(0, states.size());
		return states.get(i);
	}

	/**
	 * Gets an action at a given index
	 *
	 * @param i Index
	 * @return Action
	 */
	public A getAction(final int i) {
		checkElementIndex(0, actions.size());
		return actions.get(i);
	}

	/**
	 * Gets all states.
	 *
	 * @return
	 */
	public List<S> getStates() {
		return states;
	}

	/**
	 * Gets all actions.
	 *
	 * @return
	 */
	public List<A> getActions() {
		return actions;
	}

	/**
	 * Creates a reversed trace by reversing both the states and the actions.
	 * The original trace is not modified.
	 *
	 * @return Reversed trace
	 */
	public Trace<S, A> reverse() {
		return Trace.of(states.reverse(), actions.reverse());
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Trace(");
		for (int i = 0; i < states.size(); ++i) {
			sb.append(getState(i));
			if (i < actions.size()) {
				sb.append(" ---[");
				sb.append(getAction(i));
				sb.append("]--> ");
			}
		}
		sb.append(')');
		return sb.toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof Trace) {
			final Trace<?, ?> that = (Trace<?, ?>) obj;
			return this.states.equals(that.states) && this.actions.equals(that.actions);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * states.hashCode() + actions.hashCode();
	}
}
