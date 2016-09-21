package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.expr.BoolLitExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public class GlobalPredItpRefinerOp<A extends Action> implements RefinerOp<PredState, A, ItpRefutation, SimplePredPrecision> {

	@Override
	public SimplePredPrecision refine(final SimplePredPrecision precision, final ItpRefutation refutation, final Trace<PredState, A> counterexample) {
		final Set<Expr<? extends BoolType>> preds = new HashSet<>();
		for (final Expr<? extends BoolType> pred : refutation) {
			if (!(pred instanceof BoolLitExpr)) {
				preds.add(pred);
			}
		}
		assert (preds.size() > 0);
		return precision.refine(preds);
	}

}
