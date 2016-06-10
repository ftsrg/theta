package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans.TCFADelayTrans;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans.TCFADiscreteTrans;

public class TCFATransferFunction<S extends State, P extends Precision>
		implements TransferFunction<TCFAState<S>, P, TCFATrans> {

	private final TransferFunction<S, P, TCFATrans> transferFunction;

	public TCFATransferFunction(final TransferFunction<S, P, TCFATrans> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	@Override
	public Collection<TCFAState<S>> getSuccStates(final TCFAState<S> state, final P precision, final TCFATrans trans) {
		checkNotNull(state);
		checkNotNull(precision);
		checkNotNull(trans);

		if (trans instanceof TCFADelayTrans) {
			return succStatesForDelayTrans(state, precision, (TCFADelayTrans) trans);
		} else if (trans instanceof TCFADiscreteTrans) {
			return succStatesForDiscreteTrans(state, precision, (TCFADiscreteTrans) trans);
		} else {
			throw new AssertionError();
		}
	}

	private Collection<TCFAState<S>> succStatesForDelayTrans(final TCFAState<S> state, final P precision,
			final TCFADelayTrans trans) {
		final Collection<TCFAState<S>> succStates = new ArrayList<>();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(state.getState(), precision,
				trans);
		for (final S subSuccState : subSuccStates) {
			final TCFAState<S> succState = TCFAState.create(state.getLoc(), subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

	private Collection<TCFAState<S>> succStatesForDiscreteTrans(final TCFAState<S> state, final P precision,
			final TCFADiscreteTrans trans) {
		final Collection<TCFAState<S>> succStates = new ArrayList<>();

		if (!state.getLoc().getOutEdges().contains(trans.getEdge())) {
			return Collections.emptySet();
		}

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(state.getState(), precision,
				trans);
		for (final S subSuccState : subSuccStates) {
			final TCFAState<S> succState = TCFAState.create(trans.getEdge().getTarget(), subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
