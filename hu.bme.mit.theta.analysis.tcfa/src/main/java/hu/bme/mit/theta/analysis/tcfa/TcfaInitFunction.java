package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

class TcfaInitFunction<S extends State, P extends Precision> implements InitFunction<TcfaState<S>, P> {

	private final TcfaLoc initLoc;
	private final InitFunction<S, P> initFunction;

	TcfaInitFunction(final TcfaLoc initLoc, final InitFunction<S, P> initFunction) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunction = checkNotNull(initFunction);
	}

	@Override
	public Collection<TcfaState<S>> getInitStates(final P precision) {
		final Collection<TcfaState<S>> initStates = new ArrayList<>();
		final Collection<? extends S> subInitStates = initFunction.getInitStates(precision);
		for (final S subInitState : subInitStates) {
			final TcfaState<S> initState = TcfaState.create(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
