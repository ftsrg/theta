package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class LocTransferFunction<S extends State, A extends LocAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements TransferFunction<LocState<S, L, E>, A, LocPrecision<P, L, E>> {

	private final TransferFunction<S, ? super A, P> transferFunction;

	private LocTransferFunction(final TransferFunction<S, ? super A, P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <S extends State, A extends LocAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocTransferFunction<S, A, P, L, E> create(
			final TransferFunction<S, ? super A, P> transferFunction) {
		return new LocTransferFunction<>(transferFunction);
	}

	@Override
	public Collection<LocState<S, L, E>> getSuccStates(final LocState<S, L, E> state, final A action,
			final LocPrecision<P, L, E> precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		final E edge = action.getEdge();
		final L source = edge.getSource();
		final L target = edge.getTarget();
		checkArgument(state.getLoc() == source);

		final Collection<LocState<S, L, E>> succStates = new ArrayList<>();

		final P subPrecision = precision.getPrecision(target);
		final S subState = state.getState();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(subState, action, subPrecision);
		for (final S subSuccState : subSuccStates) {
			final LocState<S, L, E> succState = LocState.create(target, subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
