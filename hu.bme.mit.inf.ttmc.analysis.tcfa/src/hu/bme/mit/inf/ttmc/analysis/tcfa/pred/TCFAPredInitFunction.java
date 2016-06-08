package hu.bme.mit.inf.ttmc.analysis.tcfa.pred;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAPredInitFunction implements InitFunction<PredState, PredPrecision, TCFALoc> {

	@Override
	public Collection<PredState> getInitStates(final PredPrecision precision, final TCFALoc init) {
		return Collections.singleton(PredState.create(Collections.emptySet()));
	}

}
