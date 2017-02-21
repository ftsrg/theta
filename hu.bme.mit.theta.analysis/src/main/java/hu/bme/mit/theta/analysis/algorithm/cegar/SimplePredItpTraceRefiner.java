package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;

public class SimplePredItpTraceRefiner<S extends ExprState, A extends ExprAction>
		implements TraceRefiner<S, A, SimplePredPrecision, ItpRefutation>,
		TraceSeqRefiner<S, A, SimplePredPrecision, ItpRefutation> {

	@Override
	public SimplePredPrecision refine(final Trace<S, A> trace, final SimplePredPrecision precision,
			final ItpRefutation refutation) {
		final SimplePredPrecision refinedPrecision = precision
				.join(SimplePredPrecision.create(refutation, precision.getSolver()));
		return refinedPrecision;
	}

	@Override
	public List<SimplePredPrecision> refine(final Trace<S, A> trace, final List<SimplePredPrecision> precisions,
			final ItpRefutation refutation) {
		final List<SimplePredPrecision> refinedPrecisions = new ArrayList<>(precisions.size());
		for (int i = 0; i < precisions.size(); ++i) {
			refinedPrecisions.add(precisions.get(i).join(SimplePredPrecision
					.create(Collections.singleton(refutation.get(i)), precisions.get(i).getSolver())));
		}
		return refinedPrecisions;
	}

}
