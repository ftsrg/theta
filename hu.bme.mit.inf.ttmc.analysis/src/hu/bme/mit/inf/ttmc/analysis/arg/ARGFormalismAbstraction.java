package hu.bme.mit.inf.ttmc.analysis.arg;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.Formalism;

public class ARGFormalismAbstraction<F extends Formalism, S extends State, P extends Precision> implements FormalismAbstraction<F, ARGState<S>, P> {

	private final FormalismAbstraction<F, S, P> formalismAbstraction;

	private ARGFormalismAbstraction(final FormalismAbstraction<F, S, P> formalismAbstraction) {
		this.formalismAbstraction = checkNotNull(formalismAbstraction);
	}

	public static <F extends Formalism, S extends State, P extends Precision> ARGFormalismAbstraction<F, S, P> create(
			final FormalismAbstraction<F, S, P> formalismAbstraction) {
		return new ARGFormalismAbstraction<>(formalismAbstraction);
	}

	@Override
	public Collection<? extends ARGState<S>> getStartStates(final P precision) {
		final Set<ARGState<S>> argStartStates = new HashSet<>();

		for (final S startState : formalismAbstraction.getStartStates(precision)) {
			final ARGState<S> argStartState = ARGState.create(startState);
			argStartStates.add(argStartState);
		}

		return argStartStates;
	}

	@Override
	public Collection<? extends ARGState<S>> getSuccStates(final ARGState<S> state, final P precision) {
		final Set<ARGState<S>> argSuccStates = new HashSet<>();

		for (final S succState : formalismAbstraction.getSuccStates(state.getState(), precision)) {
			final ARGState<S> argSuccState = ARGState.create(succState, state);
			state.addSuccessor(argSuccState);
			argSuccStates.add(argSuccState);
		}

		return argSuccStates;
	}

	@Override
	public boolean isTarget(final ARGState<S> state) {
		final boolean isTarget = formalismAbstraction.isTarget(state.getState());
		state.setTarget(isTarget);
		return isTarget;
	}

}
