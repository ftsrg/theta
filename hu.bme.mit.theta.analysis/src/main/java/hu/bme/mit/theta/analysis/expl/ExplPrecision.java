package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.core.model.impl.Valuation;

public interface ExplPrecision extends Precision {

	public ExplState mapToAbstractState(final Valuation valuation);
}
