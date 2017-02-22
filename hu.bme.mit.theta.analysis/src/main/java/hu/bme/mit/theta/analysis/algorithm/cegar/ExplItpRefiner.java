package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class ExplItpRefiner<S extends State, A extends Action>
		implements PrecRefiner<S, A, ExplPrecision, ItpRefutation> {

	@Override
	public ExplPrecision refine(final Trace<S, A> trace, final ExplPrecision precision,
			final ItpRefutation refutation) {
		final ExplPrecision refinedPrecision = precision.join(ExplPrecision.create(ExprUtils.getVars(refutation)));
		return refinedPrecision;
	}
}
