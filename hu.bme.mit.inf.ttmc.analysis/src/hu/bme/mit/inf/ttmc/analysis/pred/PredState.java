package hu.bme.mit.inf.ttmc.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredState implements State<PredState> {

	private static final int HASH_SEED = 7621;

	private final Solver solver;
	private final Set<Expr<? extends BoolType>> preds;

	private volatile int hashCode;

	private PredState(final Collection<Expr<? extends BoolType>> preds, final Solver solver) {
		this.solver = checkNotNull(solver);
		this.preds = new HashSet<>(checkNotNull(preds));
	}

	public static PredState create(final Collection<Expr<? extends BoolType>> preds, final Solver solver) {
		return new PredState(preds, solver);
	}

	public Collection<Expr<? extends BoolType>> getPreds() {
		return Collections.unmodifiableCollection(preds);
	}

	@Override
	public PredState join(final PredState state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public boolean isLeq(final PredState state) {
		solver.push();
		solver.add(preds);
		solver.add(Exprs.Not(Exprs.And(state.getPreds())));
		final boolean result = !solver.check().boolValue();
		solver.pop();
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
