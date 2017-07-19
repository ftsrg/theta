package hu.bme.mit.theta.analysis.zone.act;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ActZoneTransferFunction<A extends Action> implements TransferFunction<ActZoneState, A, ZonePrec> {

	private final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction;

	private ActZoneTransferFunction(final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <A extends Action> ActZoneTransferFunction<A> create(
			final TransferFunction<ZoneState, ? super A, ZonePrec> transferFunction) {
		return new ActZoneTransferFunction<>(transferFunction);
	}

	@Override
	public Collection<ActZoneState> getSuccStates(final ActZoneState state, final A action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getZone();
		final Collection<? extends ZoneState> subSuccStates = transferFunction.getSuccStates(subState, action, prec);

		if (subSuccStates.isEmpty()) {
			final ActZoneState succState = ActZoneState.of(ZoneState.bottom(), ImmutableSet.of());
			return Collections.singleton(succState);
		} else {
			final Collection<ActZoneState> result = new ArrayList<>(subSuccStates.size());
			for (final ZoneState subSuccState : subSuccStates) {
				final ActZoneState succState = ActZoneState.of(subSuccState, ImmutableSet.of());
				result.add(succState);
			}
			return result;
		}
	}

}
