package hu.bme.mit.inf.ttmc.analysis.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.State;

public class CounterexampleImpl<S extends State, A extends Action> implements Counterexample<S, A> {

	private final List<S> states;
	private final List<A> actions;

	public CounterexampleImpl(final List<? extends S> states, final List<? extends A> actions) {
		checkNotNull(states);
		checkNotNull(actions);
		checkArgument(states.size() > 0);
		checkArgument(states.size() == actions.size() + 1);
		this.states = new ArrayList<S>(states);
		this.actions = new ArrayList<A>(actions);
	}

	@Override
	public int size() {
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
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Counterexample(");
		for (int i = 0; i < size(); ++i) {
			sb.append("S(").append(getState(i).toString()).append(")");
			if (i < size() - 1) {
				sb.append("; A(");
				sb.append(getAction(i));
				sb.append("); ");
			}
		}
		sb.append(")");
		return sb.toString();
	}

	@Override
	public List<S> getStates() {
		return Collections.unmodifiableList(states);
	}

	@Override
	public List<A> getActions() {
		return Collections.unmodifiableList(actions);
	}
}
