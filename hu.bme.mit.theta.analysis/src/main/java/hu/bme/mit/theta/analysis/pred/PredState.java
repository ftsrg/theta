package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.StringJoiner;

import hu.bme.mit.theta.analysis.ExprState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;

public class PredState implements ExprState {

	private static final int HASH_SEED = 7621;

	private final Set<Expr<? extends BoolType>> preds;

	private volatile Expr<? extends BoolType> expr = null;

	private volatile int hashCode;

	// Constructor does not copy the set, the static initializers should do the copying
	private PredState(final Set<Expr<? extends BoolType>> preds) {
		this.preds = checkNotNull(preds);
	}

	public static PredState create(final Collection<Expr<? extends BoolType>> preds) {
		return new PredState(new HashSet<>(checkNotNull(preds)));
	}

	public Collection<Expr<? extends BoolType>> getPreds() {
		return Collections.unmodifiableCollection(preds);
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
