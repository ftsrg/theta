package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;

final class TCFAZoneTransferFunction implements TransferFunction<ZoneState, TCFAAction, ZonePrecision> {

	private static TCFAZoneTransferFunction INSTANCE = new TCFAZoneTransferFunction();

	private TCFAZoneTransferFunction() {
	}

	static TCFAZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final TCFAAction action,
			final ZonePrecision precision) {
		final ZoneState.ZoneOperations succStateBuilder = state.transform();

		succStateBuilder.up();
		for (final ClockOp op : action.getClockOps()) {
			succStateBuilder.execute(op);
		}
		for (final ClockConstr invar : action.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}
		succStateBuilder.norm(precision.asMap());

		final ZoneState succState = succStateBuilder.done();

		if (succState.isBottom()) {
			return ImmutableSet.of();
		} else {
			return ImmutableSet.of(succState);
		}
	}

}
