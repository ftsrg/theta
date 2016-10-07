package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public final class SimplePredPrecision implements PredPrecision {

	private final Map<Expr<? extends BoolType>, Expr<? extends BoolType>> predToNegMap;

	public static SimplePredPrecision create(final Collection<Expr<? extends BoolType>> preds) {
		return new SimplePredPrecision(preds);
	}

	private SimplePredPrecision(final Collection<Expr<? extends BoolType>> preds) {
		checkNotNull(preds);
		this.predToNegMap = new HashMap<>();

		for (final Expr<? extends BoolType> pred : preds) {
			final Expr<? extends BoolType> ponatedPred = ExprUtils.ponate(pred);
			if (!this.predToNegMap.containsKey(ponatedPred)) {
				this.predToNegMap.put(ponatedPred, Exprs.Not(ponatedPred));
			}
		}
	}

	private Expr<? extends BoolType> negate(final Expr<? extends BoolType> pred) {
		final Expr<? extends BoolType> negated = predToNegMap.get(pred);
		checkArgument(negated != null);
		return negated;
	}

	@Override
	public PredState createState(final Valuation valuation) {
		checkNotNull(valuation);
		final Set<Expr<? extends BoolType>> statePreds = new HashSet<>();

		for (final Expr<? extends BoolType> pred : predToNegMap.keySet()) {
			final LitExpr<? extends BoolType> predHolds = ExprUtils.evaluate(pred, valuation);
			if (predHolds.equals(Exprs.True())) {
				statePreds.add(pred);
			} else {
				statePreds.add(negate(pred));
			}
		}

		return PredState.create(statePreds);
	}

	public SimplePredPrecision refine(final Collection<Expr<? extends BoolType>> extraPreds) {
		checkNotNull(extraPreds);
		final Set<Expr<? extends BoolType>> joinedPreds = new HashSet<>();
		joinedPreds.addAll(this.predToNegMap.keySet());
		joinedPreds.addAll(extraPreds);
		return create(joinedPreds);
	}

	public SimplePredPrecision refine(final Expr<? extends BoolType> extraPred) {
		return refine(Collections.singleton(extraPred));
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("SimplePredPrecision").addAll(predToNegMap.keySet()).toString();
	}
}
