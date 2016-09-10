package hu.bme.mit.theta.splittingcegar.common.data;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

public class KripkeStructure<T> {
	private final List<T> states;
	private final List<T> initialStates;

	public KripkeStructure() {
		states = new ArrayList<T>();
		initialStates = new ArrayList<T>();
	}

	public List<T> getStates() {
		return states;
	}

	public T getState(final int i) {
		checkArgument(0 <= i && i < states.size());
		return states.get(i);
	}

	public List<T> getInitialStates() {
		return initialStates;
	}

	public T getInitialState(final int i) {
		checkArgument(0 <= i && i < initialStates.size());
		return initialStates.get(i);
	}

	public void addState(final T state) {
		checkNotNull(state);
		states.add(state);
	}

	public void addInitialState(final T state) {
		checkNotNull(state);
		initialStates.add(state);
	}

}
