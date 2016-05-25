package hu.bme.mit.inf.ttmc.analysis.algorithm.refiner.impl;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.algorithm.refiner.Refiner;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.pred.precisions.GlobalPredPrecision;
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.core.expr.BoolLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class PredGlobalItpRefiner implements Refiner<PredState, GlobalPredPrecision, ItpRefutation> {

	private static final PredGlobalItpRefiner INSTANCE;

	static {
		INSTANCE = new PredGlobalItpRefiner();
	}

	private PredGlobalItpRefiner() {

	}

	public static PredGlobalItpRefiner create() {
		return INSTANCE;
	}

	@Override
	public GlobalPredPrecision refine(final GlobalPredPrecision precision, final ItpRefutation refutation) {
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
