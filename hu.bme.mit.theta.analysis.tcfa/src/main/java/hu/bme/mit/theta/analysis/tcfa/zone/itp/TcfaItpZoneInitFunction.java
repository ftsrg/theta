package hu.bme.mit.theta.analysis.tcfa.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaItpZoneInitFunction implements InitFunction<ItpZoneState, ZonePrecision> {

	private static final TcfaItpZoneInitFunction INSTANCE = new TcfaItpZoneInitFunction();

	private TcfaItpZoneInitFunction() {
	}

	public static TcfaItpZoneInitFunction getInstance() {
		return INSTANCE;
	}

	////

	@Override
	public Collection<? extends ItpZoneState> getInitStates(final ZonePrecision precision) {
		checkNotNull(precision);
		return Collections.singleton(ItpZoneState.of(ZoneState.top(), ZoneState.top()));
	}

}
