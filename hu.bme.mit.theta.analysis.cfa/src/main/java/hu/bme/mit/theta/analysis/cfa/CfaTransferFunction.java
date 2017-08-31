package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

final class CfaTransferFunction<S extends ExprState, P extends Prec>
		implements TransferFunction<CfaState<S>, CfaAction, CfaPrec<P>> {

	private final TransferFunction<S, ? super CfaAction, ? super P> transferFunction;

	private CfaTransferFunction(final TransferFunction<S, ? super CfaAction, ? super P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <S extends ExprState, P extends Prec> CfaTransferFunction<S, P> create(
			final TransferFunction<S, ? super CfaAction, ? super P> transferFunction) {
		return new CfaTransferFunction<>(transferFunction);
	}

	@Override
	public Collection<CfaState<S>> getSuccStates(final CfaState<S> state, final CfaAction action,
			final CfaPrec<P> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final Edge edge = action.getEdge();
		final Loc source = edge.getSource();
		final Loc target = edge.getTarget();
		checkArgument(state.getLoc().equals(source), "Location mismatch");

		final Collection<CfaState<S>> succStates = new ArrayList<>();

		final P subPrec = prec.getPrec(target);
		final S subState = state.getState();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(subState, action, subPrec);
		for (final S subSuccState : subSuccStates) {
			final CfaState<S> succState = CfaState.of(target, subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
