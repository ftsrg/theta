package hu.bme.mit.theta.analysis.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.zone.BoundFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class LuZoneTransferFunction<A extends Action> implements TransferFunction<LuZoneState, A, ZonePrec> {

	private final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction;

	private LuZoneTransferFunction(final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <A extends Action> LuZoneTransferFunction<A> create(
			final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction) {
		return new LuZoneTransferFunction<>(transferFunction);
	}

	@Override
	public Collection<LuZoneState> getSuccStates(final LuZoneState state, final A action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getZone();
		final Collection<? extends ZoneState> subSuccStates = transferFunction.getSuccStates(subState, action, prec);

		if (subSuccStates.isEmpty()) {
			final LuZoneState succState = LuZoneState.of(ZoneState.bottom(), BoundFunction.top());
			return Collections.singleton(succState);
		} else {
			final Collection<LuZoneState> result = new ArrayList<>(subSuccStates.size());
			for (final ZoneState subSuccState : subSuccStates) {
				final LuZoneState succState = LuZoneState.of(subSuccState, BoundFunction.top());
				result.add(succState);
			}
			return result;
		}
	}

}
