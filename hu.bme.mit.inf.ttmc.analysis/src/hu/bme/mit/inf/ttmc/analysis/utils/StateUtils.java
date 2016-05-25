package hu.bme.mit.inf.ttmc.analysis.utils;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeState;

public final class StateUtils {

	private StateUtils() {
	}

	public static <S extends State> Optional<S> extract(final State state, final Class<S> stateType) {
		if (stateType.isInstance(stateType)) {
			@SuppressWarnings("unchecked")
			final S foundState = (S) state;
			return Optional.of(foundState);

		} else if (state instanceof CompositeState) {
			final CompositeState<?, ?> compState = (CompositeState<?, ?>) state;

			final Optional<S> leftResult = extract(compState._1(), stateType);
			if (leftResult.isPresent()) {
				return leftResult;
			}

			final Optional<S> rightResult = extract(compState._2(), stateType);
			if (rightResult.isPresent()) {
				return rightResult;
			}
		}

		return Optional.empty();
	}

}
