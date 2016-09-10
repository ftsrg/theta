package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public class TraceImpl<S extends State, A extends Action> implements Trace<S, A> {

	private final List<S> states;
	private final List<A> actions;

	public TraceImpl(final List<? extends S> states, final List<? extends A> actions) {
		checkNotNull(states);
		checkNotNull(actions);
		checkArgument(states.size() > 0);
		checkArgument(states.size() == actions.size() + 1);
		this.states = new ArrayList<>(states);
		this.actions = new ArrayList<>(actions);
	}

	@Override
	public int length() {
		return states.size();
	}

	@Override
	public S getState(final int i) {
		checkElementIndex(0, states.size());
		return states.get(i);
	}

	@Override
	public A getAction(final int i) {
		checkElementIndex(0, actions.size());
		return actions.get(i);
	}

	@Override
	public List<S> getStates() {
		return Collections.unmodifiableList(states);
	}

	@Override
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
