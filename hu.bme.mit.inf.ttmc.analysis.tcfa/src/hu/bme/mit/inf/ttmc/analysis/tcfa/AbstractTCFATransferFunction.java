package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADelayAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADiscreteAction;

public abstract class AbstractTCFATransferFunction<S extends State, P extends Precision>
		implements TransferFunction<S, TCFAAction, P> {

	@Override
	public Collection<? extends S> getSuccStates(final S state, final TCFAAction action, final P precision) {
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

	protected abstract Collection<? extends S> succStatesForDelayTrans(final S state, final TCFADelayAction action,
			final P precision);

	protected abstract Collection<? extends S> succStatesForDiscreteTrans(final S state,
			final TCFADiscreteAction action, final P precision);

}
