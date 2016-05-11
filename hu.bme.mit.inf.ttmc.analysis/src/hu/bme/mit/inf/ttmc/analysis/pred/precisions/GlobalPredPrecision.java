package hu.bme.mit.inf.ttmc.analysis.pred.precisions;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class GlobalPredPrecision implements PredPrecision {
	private final Map<Expr<? extends BoolType>, Expr<? extends BoolType>> preds;

	public static GlobalPredPrecision create(final Collection<Expr<? extends BoolType>> preds) {
		return new GlobalPredPrecision(preds);
	}

	private GlobalPredPrecision(final Collection<Expr<? extends BoolType>> preds) {
		checkNotNull(preds);
		this.preds = new HashMap<>();

		for (final Expr<? extends BoolType> pred : preds) {
			final Expr<? extends BoolType> predSimplified = ExprUtils.ponate(pred);
			if (!this.preds.containsKey(predSimplified)) {
				this.preds.put(predSimplified, Exprs.Not(predSimplified));
			}
		}
	}

	private Expr<? extends BoolType> negate(final Expr<? extends BoolType> pred) {
		final Expr<? extends BoolType> negated = preds.get(pred);
		checkArgument(negated != null);
		return negated;
	}

	@Override
	public PredState mapToAbstractState(final Valuation valuation) {
		checkNotNull(valuation);
		final Set<Expr<? extends BoolType>> statePreds = new HashSet<>();

		for (final Expr<? extends BoolType> pred : preds.keySet()) {
			final LitExpr<? extends BoolType> predHolds = FormalismUtils.evaluate(pred, valuation);
			if (predHolds.equals(Exprs.True())) {
				statePreds.add(pred);
			} else {
				statePreds.add(negate(pred));
			}
		}

		return PredState.create(statePreds);
	}
}
