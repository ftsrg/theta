package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaLoc;

class TCFAInitFunction<S extends State, P extends Precision> implements InitFunction<TCFAState<S>, P> {

	private final TcfaLoc initLoc;
	private final InitFunction<S, P> initFunction;

	TCFAInitFunction(final TcfaLoc initLoc, final InitFunction<S, P> initFunction) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunction = checkNotNull(initFunction);
	}

	@Override
	public Collection<TCFAState<S>> getInitStates(final P precision) {
		final Collection<TCFAState<S>> initStates = new ArrayList<>();
		final Collection<? extends S> subInitStates = initFunction.getInitStates(precision);
		for (final S subInitState : subInitStates) {
			final TCFAState<S> initState = TCFAState.create(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
