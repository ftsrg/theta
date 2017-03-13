package hu.bme.mit.theta.analysis.tcfa.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaLuZoneInitFunction implements InitFunction<LuZoneState, ZonePrec> {
	private static final TcfaLuZoneInitFunction INSTANCE = new TcfaLuZoneInitFunction();

	private TcfaLuZoneInitFunction() {
	}

	public static TcfaLuZoneInitFunction getInstance() {
		return INSTANCE;
	}

	////

	@Override
	public Collection<? extends LuZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		return Collections.singleton(LuZoneState.of(ZoneState.top(), BoundFunction.top()));
	}

}
