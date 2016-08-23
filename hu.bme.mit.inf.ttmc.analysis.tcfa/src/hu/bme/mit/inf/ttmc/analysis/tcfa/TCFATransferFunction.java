package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaEdge;

class TCFATransferFunction<S extends State, P extends Precision>
		implements TransferFunction<TCFAState<S>, TCFAAction, P> {

	private final TransferFunction<S, TCFAAction, P> transferFunction;

	TCFATransferFunction(final TransferFunction<S, TCFAAction, P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	@Override
	public Collection<? extends TCFAState<S>> getSuccStates(final TCFAState<S> state, final TCFAAction action,
			final P precision) {
		final TcfaEdge edge = action.getEdge();
		checkArgument(state.getLoc().getOutEdges().contains(edge));

		final Collection<TCFAState<S>> succStates = new ArrayList<>();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(state.getState(), action,
				precision);
		for (final S subSuccState : subSuccStates) {
			final TCFAState<S> succState = TCFAState.create(edge.getTarget(), subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
