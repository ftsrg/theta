package hu.bme.mit.inf.ttmc.analysis.tcfa.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.common.Unit;

public class TCFAPredInitFunction implements InitFunction<PredState, PredPrecision, Unit> {

	@Override
	public Collection<PredState> getInitStates(final PredPrecision precision, final Unit init) {
		checkNotNull(precision);
		checkNotNull(init);
		return Collections.singleton(PredState.create(Collections.emptySet()));
	}

}
