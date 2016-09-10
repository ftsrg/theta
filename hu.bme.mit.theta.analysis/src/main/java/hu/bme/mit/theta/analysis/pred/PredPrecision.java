package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.formalism.common.Valuation;

public interface PredPrecision extends Precision {
	public PredState mapToAbstractState(final Valuation valuation);
}
