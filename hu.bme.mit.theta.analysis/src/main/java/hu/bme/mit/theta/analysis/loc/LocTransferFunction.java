package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

final class LocTransferFunction<S extends State, A extends LocAction<L, E>, P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>>
		implements TransferFunction<LocState<S, L, E>, A, LocPrec<P, L, E>> {

	private final TransferFunction<S, ? super A, ? super P> transferFunction;

	private LocTransferFunction(final TransferFunction<S, ? super A, ? super P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <S extends State, A extends LocAction<L, E>, P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> LocTransferFunction<S, A, P, L, E> create(
			final TransferFunction<S, ? super A, ? super P> transferFunction) {
		return new LocTransferFunction<>(transferFunction);
	}

	@Override
	public Collection<LocState<S, L, E>> getSuccStates(final LocState<S, L, E> state, final A action,
			final LocPrec<P, L, E> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final E edge = action.getEdge();
		final L source = edge.getSource();
		final L target = edge.getTarget();
		checkArgument(state.getLoc().equals(source));

		final Collection<LocState<S, L, E>> succStates = new ArrayList<>();

		final P subPrec = prec.getPrec(target);
		final S subState = state.getState();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(subState, action, subPrec);
		for (final S subSuccState : subSuccStates) {
			final LocState<S, L, E> succState = LocState.of(target, subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
