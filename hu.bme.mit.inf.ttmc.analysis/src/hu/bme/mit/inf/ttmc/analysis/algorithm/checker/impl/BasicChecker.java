package hu.bme.mit.inf.ttmc.analysis.algorithm.checker.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.checker.Checker;
import hu.bme.mit.inf.ttmc.analysis.algorithm.checker.waitlist.Waitlist;
import hu.bme.mit.inf.ttmc.analysis.algorithm.checker.waitlist.impl.FIFOWaitlist;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGDomain;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGFormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGState;
import hu.bme.mit.inf.ttmc.analysis.impl.CounterexampleImpl;
import hu.bme.mit.inf.ttmc.formalism.Formalism;

public class BasicChecker<F extends Formalism, S extends State, P extends Precision> implements Checker<F, S, P> {

	private final ARGDomain<S> domain;
	private final ARGFormalismAbstraction<F, S, P> formalismAbstraction;
	private final Waitlist<ARGState<S>> waitlist;

	private BasicChecker(final Domain<S> domain, final FormalismAbstraction<F, S, P> formalismAbstraction) {
		this.domain = ARGDomain.create(checkNotNull(domain));
		this.formalismAbstraction = ARGFormalismAbstraction.create(checkNotNull(formalismAbstraction));
		this.waitlist = new FIFOWaitlist<>();
	}

	public static <F extends Formalism, S extends State, P extends Precision> BasicChecker<F, S, P> create(final Domain<S> domain,
			final FormalismAbstraction<F, S, P> formalismAbstraction) {
		return new BasicChecker<>(domain, formalismAbstraction);
	}

	@Override
	public Optional<Counterexample<S>> check(final P precision) {
		waitlist.clear();
		final Collection<? extends ARGState<S>> reachedSet = formalismAbstraction.getStartStates(precision);
		waitlist.addAll(reachedSet);
		final Deque<ARGState<S>> reached = new ArrayDeque<ARGState<S>>(reachedSet);

		ARGState<S> targetState = null;

		while (!waitlist.isEmpty() && targetState == null) {
			final ARGState<S> state = waitlist.remove();

			if (formalismAbstraction.isTarget(state)) {
				targetState = state;
			}

			if (targetState == null) {
				for (final ARGState<S> succState : formalismAbstraction.getSuccStates(state, precision)) {
					if (!isCovered(succState, reached)) {
						waitlist.add(succState);
						reached.add(succState);
					}
				}
			}
		}

		if (targetState == null) {
			return Optional.empty();
		} else {
			final List<S> path = new ArrayList<>();
			Optional<ARGState<S>> iterator = Optional.of(targetState);
			while (iterator.isPresent()) {
				path.add(0, iterator.get().getState());
				iterator = iterator.get().getParent();
			}
			return Optional.of(CounterexampleImpl.create(path));
		}

	}

	private boolean isCovered(final ARGState<S> state, final Collection<? extends ARGState<S>> reached) {
		return reached.stream().anyMatch(s -> domain.isLeq(state, s));
	}

}
