package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;

final class TcfaZoneTransferFunction implements TransferFunction<ZoneState, TcfaAction, ZonePrecision> {

	private static TcfaZoneTransferFunction INSTANCE = new TcfaZoneTransferFunction();

	private TcfaZoneTransferFunction() {
	}

	static TcfaZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final TcfaAction action,
			final ZonePrecision precision) {

		final ZoneState succState = post(state, action, precision);

		if (succState.isBottom()) {
			return ImmutableSet.of();
		} else {
			return ImmutableSet.of(succState);
		}
	}

	ZoneState post(final ZoneState state, final TcfaAction action, final ZonePrecision precision) {
		final ZoneState.ZoneOperations succStateBuilder = state.transform();

		if (!action.getEdge().getSource().isUrgent()) {
			succStateBuilder.up();
		}

		for (final ClockConstr invar : action.getSourceClockInvars()) {
			succStateBuilder.and(invar);
		}

		for (final ClockOp op : action.getClockOps()) {
			succStateBuilder.execute(op);
		}

		for (final ClockConstr invar : action.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}

		succStateBuilder.norm(precision.asMap());

		return succStateBuilder.done();
	}

}
