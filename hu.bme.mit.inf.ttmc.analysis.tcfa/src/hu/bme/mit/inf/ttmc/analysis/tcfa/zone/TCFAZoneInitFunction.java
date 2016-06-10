package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.common.Unit;

public class TCFAZoneInitFunction implements InitFunction<ZoneState, ZonePrecision, Unit> {

	@Override
	public Collection<ZoneState> getInitStates(final ZonePrecision precision, final Unit init) {
		checkNotNull(precision);
		checkNotNull(init);
		return Collections.singleton(ZoneState.zero(precision.getClocks()));
	}

}
