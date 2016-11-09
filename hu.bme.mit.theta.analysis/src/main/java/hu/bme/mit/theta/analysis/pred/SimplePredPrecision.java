package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.Iterables;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.solver.Solver;

public final class SimplePredPrecision implements PredPrecision {

	private final Map<Expr<? extends BoolType>, Expr<? extends BoolType>> predToNegMap;
	private final Solver solver;

	public static SimplePredPrecision create(final Iterable<Expr<? extends BoolType>> preds, final Solver solver) {
		return new SimplePredPrecision(preds, solver);
	}

	private SimplePredPrecision(final Iterable<Expr<? extends BoolType>> preds, final Solver solver) {
		checkNotNull(preds);
		this.solver = checkNotNull(solver);
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
			final Expr<? extends BoolType> simplified = ExprUtils.simplify(pred, valuation);
			if (simplified.equals(Exprs.True())) {
				statePreds.add(pred);
			} else if (simplified.equals(Exprs.False())) {
				statePreds.add(negate(pred));
			} else {
				final Expr<? extends BoolType> simplified0 = PathUtils.unfold(simplified, 0);

				solver.push();
				solver.add(Exprs.Not(simplified0));
				final boolean ponValid = solver.check().isUnsat();
				solver.pop();

				solver.push();
				solver.add(simplified0);
				final boolean negValid = solver.check().isUnsat();
				solver.pop();

				assert !(ponValid && negValid);
				if (ponValid) {
					statePreds.add(pred);
				} else {
					statePreds.add(negate(pred));
				}
			}
		}

		return PredState.of(statePreds);
	}

	public SimplePredPrecision refine(final Iterable<Expr<? extends BoolType>> extraPreds) {
		checkNotNull(extraPreds);
		final Set<Expr<? extends BoolType>> joinedPreds = new HashSet<>();
		joinedPreds.addAll(this.predToNegMap.keySet());
		Iterables.addAll(joinedPreds, extraPreds);
		return create(joinedPreds, solver);
	}

	public SimplePredPrecision refine(final Expr<? extends BoolType> extraPred) {
		return refine(Collections.singleton(extraPred));
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(predToNegMap.keySet()).toString();
	}
}
