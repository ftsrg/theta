package hu.bme.mit.inf.ttmc.analysis.algorithm.impl.checker;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Checker;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.checker.waitlist.Waitlist;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.checker.waitlist.impl.FIFOWaitlist;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGDomain;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGFormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGState;
import hu.bme.mit.inf.ttmc.analysis.impl.CounterexampleImpl;
import hu.bme.mit.inf.ttmc.formalism.Formalism;

public class BasicChecker<F extends Formalism, S extends State, P extends Precision> implements Checker<F, S, P> {

	private final ARGDomain<S> domain;
	private final ARGFormalismAbstraction<F, S, P> formalismAbstraction;
	private final Waitlist<ARGState<S>> waitlist;
	private final Deque<ARGState<S>> reached;

	private BasicChecker(final Domain<S> domain, final FormalismAbstraction<F, S, P> formalismAbstraction) {
		this.domain = ARGDomain.create(checkNotNull(domain));
		this.formalismAbstraction = ARGFormalismAbstraction.create(checkNotNull(formalismAbstraction));
		this.waitlist = new FIFOWaitlist<>();
		this.reached = new ArrayDeque<ARGState<S>>();
	}

	public static <F extends Formalism, S extends State, P extends Precision> BasicChecker<F, S, P> create(final Domain<S> domain,
			final FormalismAbstraction<F, S, P> formalismAbstraction) {
		return new BasicChecker<>(domain, formalismAbstraction);
	}

	@Override
	public Optional<Counterexample<S>> check(final P precision) {
		waitlist.clear();
		reached.clear();

		final Collection<? extends ARGState<S>> reachedSet = formalismAbstraction.getStartStates(precision);
		waitlist.addAll(reachedSet);
		reached.addAll(reachedSet);

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

	@Override
	public Collection<S> getReachedSet() {
		// TODO: this may not be the optimal solution. But we cannot simly return an immutable
		// view of 'reached' because it stores 'ArgState<S>' and we have to return a collection of 'S'
		return reached.stream().map(s -> s.getState()).collect(Collectors.toSet());
	}

}
