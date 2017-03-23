package hu.bme.mit.theta.analysis.tcfa.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaItpZoneTransferFunction implements TransferFunction<ItpZoneState, TcfaAction, ZonePrec> {

	private static final TcfaItpZoneTransferFunction INSTANCE = new TcfaItpZoneTransferFunction();

	private TcfaItpZoneTransferFunction() {
	}

	public static TcfaItpZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	////

	@Override
	public Collection<? extends ItpZoneState> getSuccStates(final ItpZoneState state, final TcfaAction action,
			final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getState();
		if (subState.isBottom()) {
			return Collections.emptySet();
		} else {
			final ZoneState succSubState = TcfaZoneUtils.post(state.getState(), action, prec);
			final ItpZoneState succState = ItpZoneState.of(succSubState, ZoneState.top());
			return Collections.singleton(succState);
		}
	}

}
