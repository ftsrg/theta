package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.core.model.impl.Valuation;

public interface PredPrecision extends Precision {
	public PredState mapToAbstractState(final Valuation valuation);
}
