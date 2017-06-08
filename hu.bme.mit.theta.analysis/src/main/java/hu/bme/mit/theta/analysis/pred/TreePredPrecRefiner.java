package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Refinement for TreePredPrec
 */
public class TreePredPrecRefiner<A extends Action> implements PrecRefiner<PredState, A, TreePredPrec, ItpRefutation> {

	@Override
	public TreePredPrec refine(final TreePredPrec prec, final Trace<PredState, A> trace,
			final ItpRefutation refutation) {
		for (int i = 0; i < trace.getStates().size(); ++i) {
			final Expr<BoolType> expr = refutation.get(i);
			if (expr.equals(True()) || expr.equals(False())) {
				continue;
			}
			prec.refine(trace.getState(i), expr);
		}
		return prec;
	}

}
