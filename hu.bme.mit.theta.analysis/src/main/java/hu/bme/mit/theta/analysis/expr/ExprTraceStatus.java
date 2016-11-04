package hu.bme.mit.theta.analysis.expr;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;

public abstract class ExprTraceStatus {

	private ExprTraceStatus() {
	}

	static Feasable feasable(final Model model, final List<? extends VarIndexing> indexings) {
		return new Feasable(model, indexings);
	}

	static Unfeasable unfeasable(final Interpolant interpolant, final List<? extends ItpMarker> markers,
			final List<? extends VarIndexing> indexings) {
		return new Unfeasable(interpolant, markers, indexings);
	}

	public abstract boolean isFeasable();

	public abstract boolean isUnfeasable();

	public abstract Feasable asFeasable();

	public abstract Unfeasable asUnfeasable();

	////

	public static final class Feasable extends ExprTraceStatus {
		private final List<Valuation> valuations;

		private Feasable(final Model model, final List<? extends VarIndexing> indexings) {
			final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
			for (final VarIndexing indexing : indexings) {
				builder.add(PathUtils.extractValuation(model, indexing));
			}
			valuations = builder.build();
		}

		public List<Valuation> getValuations() {
			return valuations;
		}

		@Override
		public boolean isFeasable() {
			return true;
		}

		@Override
		public boolean isUnfeasable() {
			return false;
		}

		@Override
		public Feasable asFeasable() {
			return this;
		}

		@Override
		public Unfeasable asUnfeasable() {
			throw new ClassCastException();
		}
	}

	////

	public static final class Unfeasable extends ExprTraceStatus {
		private final List<Expr<? extends BoolType>> exprs;

		private Unfeasable(final Interpolant interpolant, final List<? extends ItpMarker> markers,
				final List<? extends VarIndexing> indexings) {
			final ImmutableList.Builder<Expr<? extends BoolType>> builder = ImmutableList.builder();
			for (int i = 0; i < markers.size(); i++) {
				final ItpMarker marker = markers.get(i);
				final VarIndexing indexing = indexings.get(i);
				builder.add(PathUtils.foldin(interpolant.eval(marker), indexing));
			}
			exprs = builder.build();
		}

		public List<Expr<? extends BoolType>> getExprs() {
			return exprs;
		}

		@Override
		public boolean isFeasable() {
			return false;
		}

		@Override
		public boolean isUnfeasable() {
			return true;
		}

		@Override
		public Feasable asFeasable() {
			throw new ClassCastException();
		}

		@Override
		public Unfeasable asUnfeasable() {
			return this;
		}
	}
}
