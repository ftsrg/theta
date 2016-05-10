package hu.bme.mit.inf.ttmc.analysis.expl;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;

public interface ExplPrecision extends Precision {

	public ExplState mapToAbstractState(final Valuation valuation);
}
