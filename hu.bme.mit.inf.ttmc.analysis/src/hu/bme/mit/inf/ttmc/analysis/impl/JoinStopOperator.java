package hu.bme.mit.inf.ttmc.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Iterator;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;

public class JoinStopOperator<S extends State, P extends Precision> implements StopOperator<S, P> {

	private final Domain<S> domain;

	public JoinStopOperator(Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	@Override
	public boolean stop(S state, Collection<S> reachedStates, P precision) {
		checkNotNull(state);
		checkNotNull(reachedStates);
		checkNotNull(precision);
		
		Iterator<S> iterator = reachedStates.iterator();
	    S joinedState = iterator.next();
	    while (iterator.hasNext()) {
	      joinedState = domain.join(iterator.next(), joinedState);
	    }

	    return domain.isLeq(state, joinedState);
	}
	
}
