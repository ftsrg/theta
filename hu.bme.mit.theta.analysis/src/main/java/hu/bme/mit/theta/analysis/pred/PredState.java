package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Set;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;

public final class PredState implements ExprState {

	private static final int HASH_SEED = 7621;

	private final Set<Expr<? extends BoolType>> preds;

	private volatile Expr<? extends BoolType> expr = null;

	private volatile int hashCode;

	private PredState(final Collection<? extends Expr<? extends BoolType>> preds) {
		checkNotNull(preds);
		this.preds = ImmutableSet.copyOf(preds);
	}

	public static PredState create(final Collection<? extends Expr<? extends BoolType>> preds) {
		return new PredState(preds);
	}

	// Convenience factory methods

	public static PredState create() {
		return new PredState(ImmutableSet.of());
	}

	public static PredState create(final Expr<? extends BoolType> pred) {
		return new PredState(ImmutableSet.of(pred));
	}

	public static PredState create(final Expr<? extends BoolType> pred1, final Expr<? extends BoolType> pred2) {
		return new PredState(ImmutableSet.of(pred1, pred2));
	}

	public static PredState create(final Expr<? extends BoolType> pred1, final Expr<? extends BoolType> pred2,
			final Expr<? extends BoolType> pred3) {
		return new PredState(ImmutableSet.of(pred1, pred2, pred3));
	}

	public static PredState create(final Expr<? extends BoolType> pred1, final Expr<? extends BoolType> pred2,
			final Expr<? extends BoolType> pred3, final Expr<? extends BoolType> pred4) {
		return new PredState(ImmutableSet.of(pred1, pred2, pred3, pred4));
	}

	public static PredState create(final Expr<? extends BoolType> pred1, final Expr<? extends BoolType> pred2,
			final Expr<? extends BoolType> pred3, final Expr<? extends BoolType> pred4,
			final Expr<? extends BoolType> pred5) {
		return new PredState(ImmutableSet.of(pred1, pred2, pred3, pred4, pred5));
	}

	////

	public Set<Expr<? extends BoolType>> getPreds() {
		return preds;
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		Expr<? extends BoolType> result = expr;
		if (result == null) {
			result = Exprs.And(preds);
			expr = result;
		}
		return result;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + preds.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof PredState) {
			final PredState that = (PredState) obj;
			return this.preds.equals(that.preds);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("PredState(");
		final String prefix = sb.toString();
		final String suffix = ")";
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (final Expr<? extends BoolType> pred : preds) {
			sj.add(pred.toString());
		}
		return sj.toString();
	}
}
