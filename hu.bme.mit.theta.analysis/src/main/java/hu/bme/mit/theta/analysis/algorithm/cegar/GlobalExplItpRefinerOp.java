package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class GlobalExplItpRefinerOp<A extends Action> implements RefinerOp<ExplState, A, ItpRefutation, ExplPrecision> {

	@Override
	public ExplPrecision refine(final ExplPrecision precision, final ItpRefutation refutation,
			final Trace<ExplState, A> counterexample) {
		return precision.with(ExprUtils.getVars(refutation));
	}

}
