package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ItpZoneTransferFunction<A extends Action> implements TransferFunction<ItpZoneState, A, ZonePrec> {

	private final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction;

	private ItpZoneTransferFunction(final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <A extends Action> ItpZoneTransferFunction<A> create(
			final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction) {
		return new ItpZoneTransferFunction<>(transferFunction);
	}

	////

	@Override
	public Collection<? extends ItpZoneState> getSuccStates(final ItpZoneState state, final A action,
			final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getState();
		final Collection<? extends ZoneState> subSuccStates = transferFunction.getSuccStates(subState, action, prec);

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
