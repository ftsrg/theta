package hu.bme.mit.inf.ttmc.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;

public class SepStopOperator<S extends State> implements StopOperator<S> {

	private final Domain<S> domain;

	public SepStopOperator(Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	@Override
	public boolean stop(S state, Collection<S> reachedStates) {
		checkNotNull(state);
		checkNotNull(reachedStates);
		
		for (S reachedState : reachedStates) {
			if (domain.isLeq(state, reachedState)) {
				return true;
			}
		}
		return false;
	}

}
