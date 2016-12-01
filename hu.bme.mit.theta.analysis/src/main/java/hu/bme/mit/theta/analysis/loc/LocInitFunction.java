package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class LocInitFunction<S extends State, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements InitFunction<LocState<S, L, E>, LocPrecision<P, L, E>> {

	private final L initLoc;
	private final InitFunction<S, P> initFunction;

	private LocInitFunction(final L initLoc, final InitFunction<S, P> initFunction) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunction = checkNotNull(initFunction);
	}

	public static <S extends State, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocInitFunction<S, P, L, E> create(
			final L initLoc, final InitFunction<S, P> initFunction) {
		return new LocInitFunction<>(initLoc, initFunction);
	}

	@Override
	public Collection<LocState<S, L, E>> getInitStates(final LocPrecision<P, L, E> precision) {
		checkNotNull(precision);

		final Collection<LocState<S, L, E>> initStates = new ArrayList<>();
		final P subPrecision = precision.getPrecision(initLoc);
		final Collection<? extends S> subInitStates = initFunction.getInitStates(subPrecision);
		for (final S subInitState : subInitStates) {
			final LocState<S, L, E> initState = LocState.of(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
