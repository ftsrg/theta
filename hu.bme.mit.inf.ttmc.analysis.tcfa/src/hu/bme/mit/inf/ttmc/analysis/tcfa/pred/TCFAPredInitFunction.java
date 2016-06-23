package hu.bme.mit.inf.ttmc.analysis.tcfa.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;

public class TCFAPredInitFunction implements InitFunction<PredState, PredPrecision> {

	@Override
	public Collection<PredState> getInitStates(final PredPrecision precision) {
		checkNotNull(precision);
		return Collections.singleton(PredState.create(Collections.emptySet()));
	}

}
