package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAZoneInitFunction implements InitFunction<ZoneState, ZonePrecision, TCFALoc> {

	@Override
	public Collection<ZoneState> getInitStates(final ZonePrecision precision, final TCFALoc init) {
		return Collections.singleton(ZoneState.zero(precision.getClocks()));
	}

}
