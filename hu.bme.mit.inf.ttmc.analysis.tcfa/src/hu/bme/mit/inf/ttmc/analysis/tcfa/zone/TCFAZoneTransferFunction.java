package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans.TCFADelayTrans;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans.TCFADiscreteTrans;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;

public class TCFAZoneTransferFunction implements TransferFunction<ZoneState, ZonePrecision, TCFATrans> {

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final ZonePrecision precision,
			final TCFATrans trans) {
		checkNotNull(state);
		checkNotNull(precision);
		checkNotNull(trans);

		if (trans instanceof TCFADelayTrans) {
			final TCFADelayTrans delayTrans = (TCFADelayTrans) trans;
			return succStatesForDelayTrans(state, precision, delayTrans);

		} else if (trans instanceof TCFADiscreteTrans) {
			final TCFADiscreteTrans discreteTrans = (TCFADiscreteTrans) trans;
			return succStatesForDiscreteTrans(state, precision, discreteTrans);

		} else {
			throw new AssertionError();
		}
	}

	private Collection<ZoneState> succStatesForDelayTrans(final ZoneState state, final ZonePrecision precision,
			final TCFADelayTrans trans) {
		final ZoneState.ZoneOperations succStateBuilder = state.transform();
		succStateBuilder.up();
		for (final ClockConstr invar : trans.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}
		return ImmutableSet.of(succStateBuilder.done());
	}

	private Collection<ZoneState> succStatesForDiscreteTrans(final ZoneState state, final ZonePrecision precision,
			final TCFADiscreteTrans trans) {
		final ZoneState.ZoneOperations succStateBuilder = state.transform();

		for (final ClockOp op : trans.getClockOps()) {
			succStateBuilder.execute(op);
		}

		for (final ClockConstr invar : trans.getTargetClockInvars()) {
			succStateBuilder.and(invar);
		}

		return ImmutableSet.of(succStateBuilder.done());
	}

}
