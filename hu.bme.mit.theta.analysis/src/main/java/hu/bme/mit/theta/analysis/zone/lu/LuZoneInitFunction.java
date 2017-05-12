package hu.bme.mit.theta.analysis.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.BoundFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class LuZoneInitFunction implements InitFunction<LuZoneState, ZonePrec> {

	private final InitFunction<ZoneState, ZonePrec> initFunction;

	private LuZoneInitFunction(final InitFunction<ZoneState, ZonePrec> initFunction) {
		this.initFunction = checkNotNull(initFunction);
	}

	public static LuZoneInitFunction create(final InitFunction<ZoneState, ZonePrec> initFunction) {
		return new LuZoneInitFunction(initFunction);
	}

	////

	@Override
	public Collection<? extends LuZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<LuZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunction.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final LuZoneState initState = LuZoneState.of(subInitState, BoundFunction.top());
			result.add(initState);
		}
		return result;
	}

}
