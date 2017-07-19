package hu.bme.mit.theta.analysis.zone.act;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ActZoneInitFunction implements InitFunction<ActZoneState, ZonePrec> {

	private final InitFunction<ZoneState, ZonePrec> initFunction;

	private ActZoneInitFunction(final InitFunction<ZoneState, ZonePrec> initFunction) {
		this.initFunction = checkNotNull(initFunction);
	}

	public static ActZoneInitFunction create(final InitFunction<ZoneState, ZonePrec> initFunction) {
		return new ActZoneInitFunction(initFunction);
	}

	////

	@Override
	public Collection<? extends ActZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<ActZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunction.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final ActZoneState initState = ActZoneState.of(subInitState, ImmutableSet.of());
			result.add(initState);
		}
		return result;
	}

}
