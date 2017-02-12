package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.core.expr.BoolLitExpr;

public class SimplePredItpTraceRefiner<S extends ExprState, A extends ExprAction>
		implements TraceRefiner<S, A, SimplePredPrecision, ItpRefutation> {

	@Override
	public SimplePredPrecision refine(final Trace<S, A> trace, final SimplePredPrecision precision,
			final ItpRefutation refutation) {
		final SimplePredPrecision refinedPrecision = precision
				.refine(refutation.stream().filter(p -> !(p instanceof BoolLitExpr)).collect(Collectors.toSet()));
		return refinedPrecision;
	}

}
