package hu.bme.mit.inf.theta.analysis.pred;

import hu.bme.mit.inf.theta.analysis.Precision;
import hu.bme.mit.inf.theta.formalism.common.Valuation;

public interface PredPrecision extends Precision {
	public PredState mapToAbstractState(final Valuation valuation);
}
