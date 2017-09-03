package hu.bme.mit.theta.analysis.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class LuZoneTransferFunc<A extends Action> implements TransferFunc<LuZoneState, A, ZonePrec> {

	private final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc;

	private LuZoneTransferFunc(final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc) {
		this.transferFunc = checkNotNull(transferFunc);
	}

	public static <A extends Action> LuZoneTransferFunc<A> create(
			final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc) {
		return new LuZoneTransferFunc<>(transferFunc);
	}

	@Override
	public Collection<LuZoneState> getSuccStates(final LuZoneState state, final A action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getZone();
		final Collection<? extends ZoneState> subSuccStates = transferFunc.getSuccStates(subState, action, prec);

		if (subSuccStates.isEmpty()) {
			final LuZoneState succState = LuZoneState.of(ZoneState.bottom(), BoundFunc.top());
			return Collections.singleton(succState);
		} else {
			final Collection<LuZoneState> result = new ArrayList<>(subSuccStates.size());
			for (final ZoneState subSuccState : subSuccStates) {
				final LuZoneState succState = LuZoneState.of(subSuccState, BoundFunc.top());
				result.add(succState);
			}
			return result;
		}
	}

}
