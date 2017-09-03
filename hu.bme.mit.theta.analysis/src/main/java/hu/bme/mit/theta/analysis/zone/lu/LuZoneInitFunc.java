package hu.bme.mit.theta.analysis.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class LuZoneInitFunc implements InitFunc<LuZoneState, ZonePrec> {

	private final InitFunc<ZoneState, ZonePrec> initFunc;

	private LuZoneInitFunc(final InitFunc<ZoneState, ZonePrec> initFunc) {
		this.initFunc = checkNotNull(initFunc);
	}

	public static LuZoneInitFunc create(final InitFunc<ZoneState, ZonePrec> initFunc) {
		return new LuZoneInitFunc(initFunc);
	}

	////

	@Override
	public Collection<? extends LuZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<LuZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunc.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final LuZoneState initState = LuZoneState.of(subInitState, BoundFunc.top());
			result.add(initState);
		}
		return result;
	}

}
