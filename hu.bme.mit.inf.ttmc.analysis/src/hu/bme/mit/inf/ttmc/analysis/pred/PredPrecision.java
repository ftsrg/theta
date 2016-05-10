package hu.bme.mit.inf.ttmc.analysis.pred;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;

public interface PredPrecision extends Precision {

	public Expr<? extends BoolType> negate(final Expr<? extends BoolType> pred);

	public PredState mapToAbstractState(final Valuation valuation);
}
