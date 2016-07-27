package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.tcfa.AbstractTCFATransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADelayAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction.TCFADiscreteAction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;

final class TCFAZoneTransferFunction extends AbstractTCFATransferFunction<ZoneState, ZonePrecision> {

	private static TCFAZoneTransferFunction INSTANCE = new TCFAZoneTransferFunction();

	private TCFAZoneTransferFunction() {
	}

	static TCFAZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	protected Collection<ZoneState> succStatesForDelayTrans(final ZoneState state, final TCFADelayAction action,
			final ZonePrecision precision) {

		final ZoneState.ZoneOperations succStateBuilder = state.transform();

		succStateBuilder.up();
		for (final ClockConstr invar : action.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}

		final ZoneState succState = succStateBuilder.done();

		if (succState.isBottom()) {
			return ImmutableSet.of();
		} else {
			return ImmutableSet.of(succState);
		}

	}

	@Override
	protected Collection<ZoneState> succStatesForDiscreteTrans(final ZoneState state, final TCFADiscreteAction action,
			final ZonePrecision precision) {
		final ZoneState.ZoneOperations succStateBuilder = state.transform();

		for (final ClockOp op : action.getClockOps()) {
			succStateBuilder.execute(op);
		}
		for (final ClockConstr invar : action.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}

		final ZoneState succState = succStateBuilder.done();

		if (succState.isBottom()) {
			return ImmutableSet.of();
		} else {
			return ImmutableSet.of(succState);
		}
	}

}
