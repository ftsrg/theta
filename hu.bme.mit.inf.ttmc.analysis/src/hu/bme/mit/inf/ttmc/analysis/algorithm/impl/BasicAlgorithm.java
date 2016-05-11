package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitStates;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;

public class BasicAlgorithm<S extends State, P extends Precision> implements Algorithm<S, P> {

	private final Domain<S> domain;
	private final InitStates<S, P> initStates;
	private final TransferRelation<S, P> transferRelation;

	public BasicAlgorithm(final Domain<S> domain, final InitStates<S, P> initStates,
			final TransferRelation<S, P> transferRelation) {
		this.domain = domain;
		this.initStates = initStates;
		this.transferRelation = transferRelation;
	}

	@Override
	public Collection<S> run(final P precision) {
		final Collection<? extends S> reachedSet = initStates.get(precision);
		final Deque<S> waitlist = new ArrayDeque<S>(reachedSet);
		final Deque<S> reached = new ArrayDeque<S>(reachedSet);

		while (!waitlist.isEmpty()) {
			final S state = waitlist.pop();

			for (final S succState : transferRelation.getSuccStates(state, precision)) {
				if (!isCovered(succState, reached)) {
					waitlist.add(succState);
					reached.add(succState);
				}
			}
		}

		return reached;
	}

	private boolean isCovered(final S state, final Collection<? extends S> reached) {
		return reached.stream().anyMatch(s -> domain.isLeq(state, s));
	}

}
