package hu.bme.mit.theta.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public final class Trace<S extends State, A extends Action> {

	private final List<S> states;
	private final List<A> actions;

	public Trace(final List<? extends S> states, final List<? extends A> actions) {
		checkNotNull(states);
		checkNotNull(actions);
		checkArgument(states.size() > 0);
		checkArgument(states.size() == actions.size() + 1);
		this.states = new ArrayList<>(states);
		this.actions = new ArrayList<>(actions);
	}

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
		return Collections.unmodifiableList(states);
	}

	public List<A> getActions() {
		return Collections.unmodifiableList(actions);
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
