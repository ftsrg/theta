package hu.bme.mit.inf.ttmc.analysis.arg;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public class ArgFormalismAbstraction<S extends State, P extends Precision> implements FormalismAbstraction<ArgState<S>, P> {

	private final FormalismAbstraction<S, P> formalismAbstraction;

	private ArgFormalismAbstraction(final FormalismAbstraction<S, P> formalismAbstraction) {
		this.formalismAbstraction = checkNotNull(formalismAbstraction);
	}

	public static <S extends State, P extends Precision> ArgFormalismAbstraction<S, P> create(final FormalismAbstraction<S, P> formalismAbstraction) {
		return new ArgFormalismAbstraction<>(formalismAbstraction);
	}

	@Override
	public Collection<? extends ArgState<S>> getStartStates(final P precision) {
		final Set<ArgState<S>> argStartStates = new HashSet<>();

		for (final S startState : formalismAbstraction.getStartStates(precision)) {
			final ArgState<S> argStartState = ArgState.create(startState);
			argStartState.setStart(true);
			argStartStates.add(argStartState);
		}

		return argStartStates;
	}

	@Override
	public Collection<? extends ArgState<S>> getSuccStates(final ArgState<S> state, final P precision) {
		final Set<ArgState<S>> argSuccStates = new HashSet<>();

		for (final S succState : formalismAbstraction.getSuccStates(state.getState(), precision)) {
			final ArgState<S> argSuccState = ArgState.create(succState, state);
			state.addSuccessor(argSuccState);
			argSuccStates.add(argSuccState);
		}

		return argSuccStates;
	}

	@Override
	public boolean isTarget(final ArgState<S> state) {
		final boolean isTarget = formalismAbstraction.isTarget(state.getState());
		state.setTarget(isTarget);
		return false;
	}

}
