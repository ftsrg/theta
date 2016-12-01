package hu.bme.mit.theta.analysis.tcfa.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaItpZoneTransferFunction implements TransferFunction<ItpZoneState, TcfaAction, ZonePrecision> {

	private static final TcfaItpZoneTransferFunction INSTANCE = new TcfaItpZoneTransferFunction();

	private TcfaItpZoneTransferFunction() {
	}

	public static TcfaItpZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	////

	@Override
	public Collection<? extends ItpZoneState> getSuccStates(final ItpZoneState state, final TcfaAction action,
			final ZonePrecision precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		final ZoneState subState = state.getState();
		if (subState.isBottom()) {
			return Collections.emptySet();
		} else {
			final ZoneState succSubState = TcfaZoneUtils.post(state.getState(), action, precision);
			final ItpZoneState succState = ItpZoneState.of(succSubState, ZoneState.top());
			return Collections.singleton(succState);
		}
	}

}
