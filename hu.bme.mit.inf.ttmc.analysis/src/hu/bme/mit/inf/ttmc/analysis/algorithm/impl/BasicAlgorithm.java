package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;

public class BasicAlgorithm<S extends State<S>> implements Algorithm<S> {

	final TransferRelation<S> transferRelation;

	public BasicAlgorithm(final TransferRelation<S> transferRelation) {
		this.transferRelation = transferRelation;
	}

	@Override
	public Collection<S> run(final Collection<? extends S> reachedSet) {
		final Deque<S> waitlist = new ArrayDeque<S>(reachedSet);
		final Deque<S> reached = new ArrayDeque<S>(reachedSet);

		while (!waitlist.isEmpty()) {
			final S state = waitlist.pop();

			for (final S succState : transferRelation.getSuccStates(state)) {
				if (!isCovered(succState, reached)) {
					waitlist.add(succState);
					reached.add(succState);
				}
			}
		}

		return reached;
	}

	private boolean isCovered(final S state, final Collection<? extends S> reached) {
		return reached.stream().anyMatch(s -> state.isLeq(s));
	}

}
