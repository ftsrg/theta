package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class ExplItpTraceRefiner<S extends ExprState, A extends ExprAction> implements
		TraceRefiner<S, A, ExplPrecision, ItpRefutation>, TraceSeqRefiner<S, A, ExplPrecision, ItpRefutation> {

	@Override
	public ExplPrecision refine(final Trace<S, A> trace, final ExplPrecision precision,
			final ItpRefutation refutation) {
		final ExplPrecision refinedPrecision = precision.join(ExplPrecision.create(ExprUtils.getVars(refutation)));
		return refinedPrecision;
	}

	@Override
	public List<ExplPrecision> refine(final Trace<S, A> trace, final List<ExplPrecision> precisions,
			final ItpRefutation refutation) {
		final List<ExplPrecision> refinedPrecisions = new ArrayList<>(precisions.size());
		for (int i = 0; i < precisions.size(); ++i) {
			refinedPrecisions.add(precisions.get(i).join(ExplPrecision.create(ExprUtils.getVars(refutation.get(i)))));
		}
		return refinedPrecisions;
	}

}
