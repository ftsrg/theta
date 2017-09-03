package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ItpZoneInitFunc implements InitFunc<ItpZoneState, ZonePrec> {

	private final InitFunc<ZoneState, ZonePrec> initFunc;

	private ItpZoneInitFunc(final InitFunc<ZoneState, ZonePrec> initFunc) {
		this.initFunc = checkNotNull(initFunc);
	}

	public static ItpZoneInitFunc create(final InitFunc<ZoneState, ZonePrec> initFunc) {
		return new ItpZoneInitFunc(initFunc);
	}

	////

	@Override
	public Collection<ItpZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<ItpZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunc.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final ItpZoneState initState = ItpZoneState.of(subInitState, ZoneState.top());
			result.add(initState);
		}
		return result;
	}

}
