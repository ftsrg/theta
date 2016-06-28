package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADelayAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADiscreteAction;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;

public class TCFATransferFunction<S extends State, P extends Precision>
		implements TransferFunction<TCFAState<S>, TCFAAction, P> {

	private final TransferFunction<S, TCFAAction, P> transferFunction;

	public TCFATransferFunction(final TransferFunction<S, TCFAAction, P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	@Override
	public Collection<TCFAState<S>> getSuccStates(final TCFAState<S> state, final TCFAAction action,
			final P precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		if (action instanceof TCFADelayAction) {
			return succStatesForDelayTrans(state, (TCFADelayAction) action, precision);
		} else if (action instanceof TCFADiscreteAction) {
			return succStatesForDiscreteTrans(state, (TCFADiscreteAction) action, precision);
		} else {
			throw new AssertionError();
		}
	}

	private Collection<TCFAState<S>> succStatesForDelayTrans(final TCFAState<S> state, final TCFADelayAction action,
			final P precision) {
		final Collection<TCFAState<S>> succStates = new ArrayList<>();

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(state.getState(), action,
				precision);
		for (final S subSuccState : subSuccStates) {
			final TCFAState<S> succState = TCFAState.create(state.getLoc(), subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

	private Collection<TCFAState<S>> succStatesForDiscreteTrans(final TCFAState<S> state,
			final TCFADiscreteAction action, final P precision) {
		final Collection<TCFAState<S>> succStates = new ArrayList<>();

		final TCFAEdge edge = action.getEdge();

		checkArgument(state.getLoc().getOutEdges().contains(edge));

		final Collection<? extends S> subSuccStates = transferFunction.getSuccStates(state.getState(), action,
				precision);
		for (final S subSuccState : subSuccStates) {
			final TCFAState<S> succState = TCFAState.create(edge.getTarget(), subSuccState);
			succStates.add(succState);
		}

		return succStates;
	}

}
