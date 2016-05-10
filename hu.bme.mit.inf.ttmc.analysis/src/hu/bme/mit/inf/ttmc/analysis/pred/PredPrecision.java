package hu.bme.mit.inf.ttmc.analysis.pred;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class PredPrecision implements Precision {
	private final Map<Expr<? extends BoolType>, Expr<? extends BoolType>> preds;

	public static PredPrecision create(final Collection<Expr<? extends BoolType>> preds) {
		return new PredPrecision(preds);
	}

	private PredPrecision(final Collection<Expr<? extends BoolType>> preds) {
		checkNotNull(preds);
		this.preds = new HashMap<>();

		for (final Expr<? extends BoolType> pred : preds) {
			if (!this.preds.containsKey(pred)) {
				this.preds.put(pred, Exprs.Not(pred));
			}
		}
	}

	public Collection<Expr<? extends BoolType>> getPreds() {
		return Collections.unmodifiableCollection(preds.keySet());
	}

	public Expr<? extends BoolType> negate(final Expr<? extends BoolType> pred) {
		final Expr<? extends BoolType> negated = preds.get(pred);
		checkArgument(negated != null);
		return negated;
	}

	public PredState mapToAbstractState(final Valuation valuation) {
		checkNotNull(valuation);
		final Set<Expr<? extends BoolType>> statePreds = new HashSet<>();

		for (final Expr<? extends BoolType> pred : getPreds()) {
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
