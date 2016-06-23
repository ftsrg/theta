package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADelayAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADiscreteAction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;

public class TCFAZoneTransferFunction implements TransferFunction<ZoneState, TCFAAction, ZonePrecision> {

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final TCFAAction action,
			final ZonePrecision precision) {
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

	private Collection<ZoneState> succStatesForDelayTrans(final ZoneState state, final TCFADelayAction action,
			final ZonePrecision precision) {
		final ZoneState.ZoneOperations succStateBuilder = state.transform();
		succStateBuilder.up();
		for (final ClockConstr invar : action.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}
		return ImmutableSet.of(succStateBuilder.done());
	}

	private Collection<ZoneState> succStatesForDiscreteTrans(final ZoneState state, final TCFADiscreteAction action,
			final ZonePrecision precision) {
		final ZoneState.ZoneOperations succStateBuilder = state.transform();

		for (final ClockOp op : action.getClockOps()) {
			succStateBuilder.execute(op);
		}

		for (final ClockConstr invar : action.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}

		return ImmutableSet.of(succStateBuilder.done());
	}

}
