package hu.bme.mit.inf.ttmc.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;

public class SepStopOperator<S extends State<S>> implements StopOperator<S> {

	@Override
	public boolean stop(final S state, final Collection<S> reachedStates) {
		checkNotNull(state);
		checkNotNull(reachedStates);
		return reachedStates.stream().anyMatch(s -> state.isLeq(s));
	}
}
