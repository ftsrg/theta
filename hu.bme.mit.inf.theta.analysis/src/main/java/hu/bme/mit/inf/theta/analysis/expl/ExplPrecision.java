package hu.bme.mit.inf.theta.analysis.expl;

import hu.bme.mit.inf.theta.analysis.Precision;
import hu.bme.mit.inf.theta.formalism.common.Valuation;

public interface ExplPrecision extends Precision {

	public ExplState mapToAbstractState(final Valuation valuation);
}
