package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ItpZoneTransferFunc<A extends Action> implements TransferFunc<ItpZoneState, A, ZonePrec> {

	private final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc;

	private ItpZoneTransferFunc(final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc) {
		this.transferFunc = checkNotNull(transferFunc);
	}

	public static <A extends Action> ItpZoneTransferFunc<A> create(
			final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc) {
		return new ItpZoneTransferFunc<>(transferFunc);
	}

	////

	@Override
	public Collection<? extends ItpZoneState> getSuccStates(final ItpZoneState state, final A action,
			final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getZone();
		final Collection<? extends ZoneState> subSuccStates = transferFunc.getSuccStates(subState, action, prec);

		if (subSuccStates.isEmpty()) {
			final ItpZoneState succState = ItpZoneState.of(ZoneState.bottom(), ZoneState.top());
			return Collections.singleton(succState);
		} else {
			final Collection<ItpZoneState> result = new ArrayList<>(subSuccStates.size());
			for (final ZoneState subSuccState : subSuccStates) {
				final ItpZoneState succState = ItpZoneState.of(subSuccState, ZoneState.top());
				result.add(succState);
			}
			return result;
		}
	}
}
