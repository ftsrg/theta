package hu.bme.mit.inf.ttmc.analysis.pred;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;

public interface PredPrecision extends Precision {
	public PredState mapToAbstractState(final Valuation valuation);
}
