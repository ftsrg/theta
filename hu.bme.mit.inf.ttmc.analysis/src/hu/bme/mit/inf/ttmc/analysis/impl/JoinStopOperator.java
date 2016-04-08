package hu.bme.mit.inf.ttmc.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;

public class JoinStopOperator<S extends State<S>> implements StopOperator<S> {

	@Override
	public boolean stop(final S state, final Collection<S> reachedStates) {
		checkNotNull(state);
		checkNotNull(reachedStates);

		final Optional<S> joinResult = reachedStates.stream().reduce((s1, s2) -> s1.join(s2));

		if (joinResult.isPresent()) {
			return state.isLeq(joinResult.get());
		} else {
			return false;
		}

	}

}
