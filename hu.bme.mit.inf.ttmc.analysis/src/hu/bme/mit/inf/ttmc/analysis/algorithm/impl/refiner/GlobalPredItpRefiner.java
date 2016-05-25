package hu.bme.mit.inf.ttmc.analysis.algorithm.impl.refiner;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Refiner;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.pred.precisions.GlobalPredPrecision;
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.core.expr.BoolLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class GlobalPredItpRefiner implements Refiner<PredState, GlobalPredPrecision, ItpRefutation> {

	private static final GlobalPredItpRefiner INSTANCE;

	static {
		INSTANCE = new GlobalPredItpRefiner();
	}

	private GlobalPredItpRefiner() {

	}

	public static GlobalPredItpRefiner create() {
		return INSTANCE;
	}

	@Override
	public GlobalPredPrecision refine(final GlobalPredPrecision precision, final Counterexample<PredState> abstractCex, final ItpRefutation refutation) {
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
