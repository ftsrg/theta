package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;

class TcfaTransferFunction<S extends State, P extends Precision>
		implements TransferFunction<TcfaState<S>, TcfaAction, P> {

	private final TransferFunction<S, TcfaAction, P> transferFunction;

	TcfaTransferFunction(final TransferFunction<S, TcfaAction, P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	@Override
	public Collection<? extends TcfaState<S>> getSuccStates(final TcfaState<S> state, final TcfaAction action,
			final P precision) {
		final TcfaEdge edge = action.getEdge();
		checkArgument(state.getLoc().getOutEdges().contains(edge));

		final Collection<TcfaState<S>> succStates = new ArrayList<>();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(state.getState(), action,
				precision);
		for (final S subSuccState : subSuccStates) {
			final TcfaState<S> succState = TcfaState.create(edge.getTarget(), subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
