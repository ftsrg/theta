package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;

public class TCFATransferFunction<S extends State, P extends Precision>
		implements TransferFunction<TCFAState<S>, P, TCFAEdge> {

	private final TransferFunction<S, P, TCFAEdge> transferFunction;

	public TCFATransferFunction(final TransferFunction<S, P, TCFAEdge> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	@Override
	public Collection<TCFAState<S>> getSuccStates(final TCFAState<S> state, final P precision, final TCFAEdge edge) {
		if (!state.getLoc().getOutEdges().contains(edge)) {
			return Collections.emptySet();
		}

		final Collection<TCFAState<S>> succStates = new ArrayList<>();
		final Collection<S> subSuccStates = transferFunction.getSuccStates(state.getState(), precision, edge);
		for (final S subSuccState : subSuccStates) {
			final TCFAState<S> succState = TCFAState.create(edge.getTarget(), subSuccState);
			succStates.add(succState);
		}
		return succStates;
	}

}
