package hu.bme.mit.theta.analysis.zone.act;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ActZoneInitFunc implements InitFunc<ActZoneState, ZonePrec> {

	private final InitFunc<ZoneState, ZonePrec> initFunc;

	private ActZoneInitFunc(final InitFunc<ZoneState, ZonePrec> initFunc) {
		this.initFunc = checkNotNull(initFunc);
	}

	public static ActZoneInitFunc create(final InitFunc<ZoneState, ZonePrec> initFunc) {
		return new ActZoneInitFunc(initFunc);
	}

	////

	@Override
	public Collection<? extends ActZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<ActZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunc.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final ActZoneState initState = ActZoneState.of(subInitState, ImmutableSet.of());
			result.add(initState);
		}
		return result;
	}

}
