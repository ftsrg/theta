package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

final class LocTransferFunction<S extends State, A extends LocAction, P extends Prec>
		implements TransferFunction<LocState<S>, A, LocPrec<P>> {

	private final TransferFunction<S, ? super A, ? super P> transferFunction;

	private LocTransferFunction(final TransferFunction<S, ? super A, ? super P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <S extends State, A extends LocAction, P extends Prec> LocTransferFunction<S, A, P> create(
			final TransferFunction<S, ? super A, ? super P> transferFunction) {
		return new LocTransferFunction<>(transferFunction);
	}

	@Override
	public Collection<LocState<S>> getSuccStates(final LocState<S> state, final A action, final LocPrec<P> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final CfaEdge edge = action.getEdge();
		final CfaLoc source = edge.getSource();
		final CfaLoc target = edge.getTarget();
		checkArgument(state.getLoc().equals(source), "Location mismatch");

		final Collection<LocState<S>> succStates = new ArrayList<>();

		final P subPrec = prec.getPrec(target);
		final S subState = state.getState();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(subState, action, subPrec);
		for (final S subSuccState : subSuccStates) {
			final LocState<S> succState = LocState.of(target, subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
