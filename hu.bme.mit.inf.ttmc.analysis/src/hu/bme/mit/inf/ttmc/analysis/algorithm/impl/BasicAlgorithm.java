package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;

public class BasicAlgorithm<S extends State, P extends Precision> implements Algorithm<S, P> {

	private final Domain<S> domain;
	private final FormalismAbstraction<S, P> formalismAbstraction;

	private boolean isErrorReached;

	public BasicAlgorithm(final Domain<S> domain, final FormalismAbstraction<S, P> formalismAbstraction) {
		this.domain = domain;
		this.formalismAbstraction = formalismAbstraction;
		this.isErrorReached = false;
	}

	@Override
	public Collection<S> run(final P precision) {
		isErrorReached = false;
		final Collection<? extends S> reachedSet = formalismAbstraction.getStartStates(precision);
		final Deque<S> waitlist = new ArrayDeque<S>(reachedSet);
		final Deque<S> reached = new ArrayDeque<S>(reachedSet);

		while (!waitlist.isEmpty()) {
			final S state = waitlist.pop();

			if (formalismAbstraction.isTarget(state)) {
				isErrorReached = true;
				return reached;
			}

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

	public boolean isErrorReached() {
		return isErrorReached;
	}

}
