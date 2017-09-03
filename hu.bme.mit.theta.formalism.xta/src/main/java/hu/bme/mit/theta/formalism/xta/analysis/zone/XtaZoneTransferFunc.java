package hu.bme.mit.theta.formalism.xta.analysis.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;

final class XtaZoneTransferFunc implements TransferFunc<ZoneState, XtaAction, ZonePrec> {

	private final static XtaZoneTransferFunc INSTANCE = new XtaZoneTransferFunc();

	private XtaZoneTransferFunc() {
	}

	static XtaZoneTransferFunc getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final XtaAction action, final ZonePrec prec) {

		final ZoneState succState = XtaZoneUtils.post(state, action, prec);

		if (succState.isBottom()) {
			return ImmutableList.of();
		} else {
			return ImmutableList.of(succState);
		}
	}

}
