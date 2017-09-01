package hu.bme.mit.theta.formalism.xta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class XtaZoneInitFunction implements InitFunction<ZoneState, ZonePrec> {

	private static final XtaZoneInitFunction INSTANCE = new XtaZoneInitFunction();

	private XtaZoneInitFunction() {
	}

	static XtaZoneInitFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		return Collections.singleton(ZoneState.zero(prec.getVars()).transform().up().build());
	}

}
