package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;
import hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.Waitlist;
import hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.impl.FIFOWaitlist;

public class BasicAlgorithm<S extends State, P extends Precision> implements Algorithm<S, P> {

	private final Domain<S> domain;
	private final FormalismAbstraction<S, P> formalismAbstraction;

	public BasicAlgorithm(final Domain<S> domain, final FormalismAbstraction<S, P> formalismAbstraction) {
		this.domain = domain;
		this.formalismAbstraction = formalismAbstraction;
	}

	@Override
	public Collection<S> run(final P precision) {
		final Collection<? extends S> reachedSet = formalismAbstraction.getStartStates(precision);
		final Waitlist<S> waitlist = new FIFOWaitlist<>(reachedSet);
		final Deque<S> reached = new ArrayDeque<S>(reachedSet);

		while (!waitlist.isEmpty()) {
			final S state = waitlist.remove();

			for (final S succState : formalismAbstraction.getSuccStates(state, precision)) {
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
