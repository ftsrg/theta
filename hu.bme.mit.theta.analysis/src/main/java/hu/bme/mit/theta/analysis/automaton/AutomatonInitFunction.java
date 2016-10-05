package hu.bme.mit.theta.analysis.automaton;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class AutomatonInitFunction<S extends State, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements InitFunction<AutomatonState<S, L, E>, AutomatonPrecision<P, L, E>> {

	private final L initLoc;
	private final InitFunction<S, P> initFunction;

	private AutomatonInitFunction(final L initLoc, final InitFunction<S, P> initFunction) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunction = checkNotNull(initFunction);
	}

	public static <S extends State, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> AutomatonInitFunction<S, P, L, E> create(
			final L initLoc, final InitFunction<S, P> initFunction) {
		return new AutomatonInitFunction<>(initLoc, initFunction);
	}

	@Override
	public Collection<AutomatonState<S, L, E>> getInitStates(final AutomatonPrecision<P, L, E> precision) {
		checkNotNull(precision);

		final Collection<AutomatonState<S, L, E>> initStates = new ArrayList<>();
		final P subPrecision = precision.getPrecision(initLoc);
		final Collection<? extends S> subInitStates = initFunction.getInitStates(subPrecision);
		for (final S subInitState : subInitStates) {
			final AutomatonState<S, L, E> initState = AutomatonState.create(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
