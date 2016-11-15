package hu.bme.mit.theta.analysis.impl;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;

public final class NullActionFunction<A extends Action> implements LTS<State, A> {

	private static final NullActionFunction<?> INSTANCE = new NullActionFunction<>();

	private NullActionFunction() {
	}

	@SuppressWarnings("unchecked")
	public static <A extends Action> NullActionFunction<A> getInstance() {
		return (NullActionFunction<A>) INSTANCE;
	}

	@Override
	public Collection<A> getEnabledActionsFor(final State state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

}
