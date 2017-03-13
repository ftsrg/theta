package hu.bme.mit.theta.analysis.tcfa.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaLuZoneTransferFunction implements TransferFunction<LuZoneState, TcfaAction, ZonePrec> {
	private static final TcfaLuZoneTransferFunction INSTANCE = new TcfaLuZoneTransferFunction();

	private TcfaLuZoneTransferFunction() {
	}

	public static TcfaLuZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<? extends LuZoneState> getSuccStates(final LuZoneState state, final TcfaAction action,
			final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState succSubState = TcfaZoneUtils.post(state.getZone(), action, prec);
		final LuZoneState succState = LuZoneState.of(succSubState, BoundFunction.top());
		return Collections.singleton(succState);
	}

}
