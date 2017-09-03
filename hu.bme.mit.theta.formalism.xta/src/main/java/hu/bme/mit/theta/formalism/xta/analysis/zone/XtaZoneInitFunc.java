package hu.bme.mit.theta.formalism.xta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class XtaZoneInitFunc implements InitFunc<ZoneState, ZonePrec> {

	private static final XtaZoneInitFunc INSTANCE = new XtaZoneInitFunc();

	private XtaZoneInitFunc() {
	}

	static XtaZoneInitFunc getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		return Collections.singleton(ZoneState.zero(prec.getVars()).transform().up().build());
	}

}
