package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ItpZoneInitFunction implements InitFunction<ItpZoneState, ZonePrec> {

	private final InitFunction<ZoneState, ZonePrec> initFunction;

	private ItpZoneInitFunction(final InitFunction<ZoneState, ZonePrec> initFunction) {
		this.initFunction = checkNotNull(initFunction);
	}

	public static ItpZoneInitFunction create(final InitFunction<ZoneState, ZonePrec> initFunction) {
		return new ItpZoneInitFunction(initFunction);
	}

	////

	@Override
	public Collection<ItpZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<ItpZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunction.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final ItpZoneState initState = ItpZoneState.of(subInitState, ZoneState.top());
			result.add(initState);
		}
		return result;
	}

}
