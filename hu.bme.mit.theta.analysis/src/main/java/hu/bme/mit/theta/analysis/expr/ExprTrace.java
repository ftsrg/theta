package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
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
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverStatus;

public final class ExprTrace {
	private final List<Expr<? extends BoolType>> exprs;
	private final List<VarIndexing> indexings;

	private ExprTrace(final List<? extends ExprAction> actions) {
		checkNotNull(actions);

		exprs = new ArrayList<>();
		indexings = new ArrayList<>();

		VarIndexing currentIndexing = VarIndexing.all(0);
		indexings.add(currentIndexing);
		for (final ExprAction action : actions) {
			exprs.add(PathUtils.unfold(action.toExpr(), currentIndexing));
			currentIndexing = currentIndexing.add(action.nextIndexing());
			indexings.add(currentIndexing);
		}
	}

	public static ExprTrace of(final List<? extends ExprAction> actions) {
		return new ExprTrace(actions);
	}

	public TraceStatus check(final ItpSolver solver) {
		solver.push();

		final List<ItpMarker> markers = new ArrayList<>();

		markers.add(solver.createMarker());
		for (final Expr<? extends BoolType> expr : exprs) {
			final ItpMarker marker = solver.createMarker();
			markers.add(marker);
			solver.add(marker, expr);
		}

		final ItpPattern pattern = solver.createSeqPattern(markers);

		final SolverStatus status = solver.check();
		final TraceStatus result;

		if (status.isSat()) {
			final Model model = solver.getModel();
			result = TraceStatus.feasable(model, indexings);
		} else {
			final Interpolant interpolant = solver.getInterpolant(pattern);
			result = TraceStatus.unfeasable(interpolant, markers, indexings);
		}
		solver.pop();

		return result;
	}

	////

	public static abstract class TraceStatus {

		private TraceStatus() {
		}

		private static Feasable feasable(final Model model, final List<? extends VarIndexing> indexings) {
			return new Feasable(model, indexings);
		}

		private static Unfeasable unfeasable(final Interpolant interpolant, final List<? extends ItpMarker> markers,
				final List<? extends VarIndexing> indexings) {
			return new Unfeasable(interpolant, markers, indexings);
		}

		public abstract boolean isFeasable();

		public abstract boolean isUnfeasable();

		public abstract Feasable asFeasable();

		public abstract Unfeasable asUnfeasable();

		////

		public static final class Feasable extends TraceStatus {
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

		public static final class Unfeasable extends TraceStatus {
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

}
