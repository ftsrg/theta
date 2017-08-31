package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

final class LocInitFunction<S extends State, P extends Prec> implements InitFunction<LocState<S>, LocPrec<P>> {

	private final Loc initLoc;
	private final InitFunction<S, ? super P> initFunction;

	private LocInitFunction(final Loc initLoc, final InitFunction<S, ? super P> initFunction) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunction = checkNotNull(initFunction);
	}

	public static <S extends State, P extends Prec> LocInitFunction<S, P> create(final Loc initLoc,
			final InitFunction<S, ? super P> initFunction) {
		return new LocInitFunction<>(initLoc, initFunction);
	}

	@Override
	public Collection<LocState<S>> getInitStates(final LocPrec<P> prec) {
		checkNotNull(prec);

		final Collection<LocState<S>> initStates = new ArrayList<>();
		final P subPrec = prec.getPrec(initLoc);
		final Collection<? extends S> subInitStates = initFunction.getInitStates(subPrec);
		for (final S subInitState : subInitStates) {
			final LocState<S> initState = LocState.of(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
