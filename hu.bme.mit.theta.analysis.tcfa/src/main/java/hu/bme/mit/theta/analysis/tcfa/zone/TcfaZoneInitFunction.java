package hu.bme.mit.theta.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;

class TcfaZoneInitFunction implements InitFunction<ZoneState, ZonePrecision> {

	private static final TcfaZoneInitFunction INSTANCE = new TcfaZoneInitFunction();

	private TcfaZoneInitFunction() {
	}

	static TcfaZoneInitFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getInitStates(final ZonePrecision precision) {
		checkNotNull(precision);
		return Collections.singleton(ZoneState.top(precision.getClocks()));
	}

}
