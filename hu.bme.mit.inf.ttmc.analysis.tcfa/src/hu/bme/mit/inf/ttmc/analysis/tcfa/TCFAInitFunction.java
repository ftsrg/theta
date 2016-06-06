package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAInitFunction<S extends State, P extends Precision> implements InitFunction<TCFAState<S>, P, TCFALoc> {

	private final InitFunction<S, P, TCFALoc> initFunction;

	public TCFAInitFunction(final InitFunction<S, P, TCFALoc> initFunction) {
		this.initFunction = checkNotNull(initFunction);
	}

	@Override
	public Collection<TCFAState<S>> getInitStates(final P precision, final TCFALoc initLoc) {
		final Collection<TCFAState<S>> initStates = new ArrayList<>();
		final Collection<S> subInitStates = initFunction.getInitStates(precision, initLoc);
		for (final S subInitState : subInitStates) {
			final TCFAState<S> initState = TCFAState.create(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
