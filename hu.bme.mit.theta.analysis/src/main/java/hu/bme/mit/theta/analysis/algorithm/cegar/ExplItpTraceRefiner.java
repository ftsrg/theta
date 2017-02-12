package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class ExplItpTraceRefiner<S extends ExprState, A extends ExprAction>
		implements TraceRefiner<S, A, ExplPrecision, ItpRefutation> {

	@Override
	public ExplPrecision refine(final Trace<S, A> trace, final ExplPrecision precision,
			final ItpRefutation refutation) {
		final ExplPrecision refinedPrecision = precision.refine(ExprUtils.getVars(refutation));
		return refinedPrecision;
	}

}
