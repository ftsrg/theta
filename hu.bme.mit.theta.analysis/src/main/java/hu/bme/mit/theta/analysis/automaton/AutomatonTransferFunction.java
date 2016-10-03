package hu.bme.mit.theta.analysis.automaton;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class AutomatonTransferFunction<S extends State, A extends AutomatonAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements TransferFunction<AutomatonState<S, L, E>, A, P> {

	private final TransferFunction<S, A, P> transferFunction;

	private AutomatonTransferFunction(final TransferFunction<S, A, P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <S extends State, A extends AutomatonAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> AutomatonTransferFunction<S, A, P, L, E> create(
			final TransferFunction<S, A, P> transferFunction) {
		return new AutomatonTransferFunction<>(transferFunction);
	}

	@Override
	public Collection<AutomatonState<S, L, E>> getSuccStates(final AutomatonState<S, L, E> state, final A action,
			final P precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		final E edge = action.getEdge();
		checkArgument(state.getLoc().getOutEdges().contains(edge));

		final Collection<AutomatonState<S, L, E>> succStates = new ArrayList<>();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(state.getState(), action,
				precision);
		for (final S subSuccState : subSuccStates) {
			final AutomatonState<S, L, E> succState = AutomatonState.create(edge.getTarget(), subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
