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
		implements TransferFunction<AutomatonState<S, L, E>, A, AutomatonPrecision<P, L, E>> {

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
			final AutomatonPrecision<P, L, E> precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		final E edge = action.getEdge();
		final L source = edge.getSource();
		final L target = edge.getTarget();
		checkArgument(state.getLoc() == source);

		final Collection<AutomatonState<S, L, E>> succStates = new ArrayList<>();

		final P subPrecision = precision.getPrecision(target);
		final S subState = state.getState();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(subState, action, subPrecision);
		for (final S subSuccState : subSuccStates) {
			final AutomatonState<S, L, E> succState = AutomatonState.create(target, subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
