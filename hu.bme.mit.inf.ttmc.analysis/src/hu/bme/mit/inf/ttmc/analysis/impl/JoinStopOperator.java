package hu.bme.mit.inf.ttmc.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;

public class JoinStopOperator<S extends State, P extends Precision> implements StopOperator<S, P> {

	private final Domain<S> domain;

	public JoinStopOperator(final Domain<S> domain) {
		this.domain = domain;
	}

	@Override
	public boolean stop(final S state, final Collection<? extends S> reachedStates, final P precision) {
		checkNotNull(state);
		checkNotNull(reachedStates);

		final Optional<? extends S> joinResult = reachedStates.stream().map(s -> (S) s)
				.reduce((s1, s2) -> domain.join(s1, s2));

		if (joinResult.isPresent()) {
			return domain.isLeq(state, joinResult.get());
		} else {
			return false;
		}

	}

}
