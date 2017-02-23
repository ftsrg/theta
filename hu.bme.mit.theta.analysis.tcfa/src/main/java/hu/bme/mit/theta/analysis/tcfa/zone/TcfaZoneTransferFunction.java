package hu.bme.mit.theta.analysis.tcfa.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaZoneTransferFunction implements TransferFunction<ZoneState, TcfaAction, ZonePrec> {

	private final static TcfaZoneTransferFunction INSTANCE = new TcfaZoneTransferFunction();

	private TcfaZoneTransferFunction() {
	}

	static TcfaZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final TcfaAction action,
			final ZonePrec prec) {

		final ZoneState succState = TcfaZoneUtils.post(state, action, prec);

		if (succState.isBottom()) {
			return ImmutableSet.of();
		} else {
			return ImmutableSet.of(succState);
		}
	}

}
