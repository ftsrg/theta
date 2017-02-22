package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;

public class SimplePredItpRefiner<S extends State, A extends Action>
		implements PrecRefiner<S, A, SimplePredPrecision, ItpRefutation> {

	@Override
	public SimplePredPrecision refine(final Trace<S, A> trace, final SimplePredPrecision precision,
			final ItpRefutation refutation) {
		final SimplePredPrecision refinedPrecision = precision
				.join(SimplePredPrecision.create(refutation, precision.getSolver()));
		return refinedPrecision;
	}
}
