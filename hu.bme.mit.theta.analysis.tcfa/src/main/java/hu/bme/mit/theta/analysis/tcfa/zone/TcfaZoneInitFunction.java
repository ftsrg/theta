package hu.bme.mit.theta.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaZoneInitFunction implements InitFunction<ZoneState, ZonePrec> {

	private static final TcfaZoneInitFunction INSTANCE = new TcfaZoneInitFunction();

	private TcfaZoneInitFunction() {
	}

	static TcfaZoneInitFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getInitStates(final ZonePrec precision) {
		checkNotNull(precision);
		return Collections.singleton(ZoneState.top());
	}

}
