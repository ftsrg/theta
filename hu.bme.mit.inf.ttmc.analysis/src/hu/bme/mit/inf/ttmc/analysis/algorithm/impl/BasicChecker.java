package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Checker;
import hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.Waitlist;
import hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.impl.FIFOWaitlist;
import hu.bme.mit.inf.ttmc.analysis.arg.ArgDomain;
import hu.bme.mit.inf.ttmc.analysis.arg.ArgFormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.arg.ArgState;

public class BasicChecker<S extends State, P extends Precision> implements Checker<S, P> {

	private final ArgDomain<S> domain;
	private final ArgFormalismAbstraction<S, P> formalismAbstraction;
	private final Waitlist<ArgState<S>> waitlist;

	private BasicChecker(final Domain<S> domain, final FormalismAbstraction<S, P> formalismAbstraction) {
		this.domain = ArgDomain.create(checkNotNull(domain));
		this.formalismAbstraction = ArgFormalismAbstraction.create(checkNotNull(formalismAbstraction));
		this.waitlist = new FIFOWaitlist<>();
	}

	public static <S extends State, P extends Precision> BasicChecker<S, P> create(final Domain<S> domain,
			final FormalismAbstraction<S, P> formalismAbstraction) {
		return new BasicChecker<>(domain, formalismAbstraction);
	}

	@Override
	public Optional<List<S>> check(final P precision) {
		waitlist.clear();
		final Collection<? extends ArgState<S>> reachedSet = formalismAbstraction.getStartStates(precision);
		waitlist.addAll(reachedSet);
		final Deque<ArgState<S>> reached = new ArrayDeque<ArgState<S>>(reachedSet);

		ArgState<S> targetState = null;

		while (!waitlist.isEmpty() && targetState == null) {
			final ArgState<S> state = waitlist.remove();

			if (formalismAbstraction.isTarget(state)) {
				targetState = state;
			}

			if (targetState == null) {
				for (final ArgState<S> succState : formalismAbstraction.getSuccStates(state, precision)) {
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
			final List<S> counterexample = new ArrayList<>();
			Optional<ArgState<S>> iterator = Optional.of(targetState);
			while (iterator.isPresent()) {
				counterexample.add(0, iterator.get().getState());
				iterator = iterator.get().getParent();
			}
			return Optional.of(counterexample);
		}

	}

	private boolean isCovered(final ArgState<S> state, final Collection<? extends ArgState<S>> reached) {
		return reached.stream().anyMatch(s -> domain.isLeq(state, s));
	}

}
