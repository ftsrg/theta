package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;

public class TreePredPrecRefiner<A extends Action> implements PrecRefiner<PredState, A, TreePredPrec, ItpRefutation> {

	@Override
	public TreePredPrec refine(final TreePredPrec prec, final Trace<PredState, A> trace,
			final ItpRefutation refutation) {
		for (int i = 0; i < trace.getStates().size(); ++i) {
			final Expr<? extends BoolType> expr = refutation.get(i);
			if (expr.equals(Exprs.True()) || expr.equals(Exprs.False()))
				continue;
			prec.refine(trace.getState(i), expr);
		}
		return prec;
	}

}
