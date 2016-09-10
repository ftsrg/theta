package hu.bme.mit.theta.analysis.tcfa.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;

class TcfaPredInitFunction implements InitFunction<PredState, PredPrecision> {

	private static final TcfaPredInitFunction INSTANCE = new TcfaPredInitFunction();

	private TcfaPredInitFunction() {
	}

	static TcfaPredInitFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<PredState> getInitStates(final PredPrecision precision) {
		checkNotNull(precision);
		return Collections.singleton(PredState.create(Collections.emptySet()));
	}

}
