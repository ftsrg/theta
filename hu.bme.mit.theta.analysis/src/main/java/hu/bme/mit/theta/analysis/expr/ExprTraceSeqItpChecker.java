package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Trace;
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

public final class ExprTraceSeqItpChecker implements ExprTraceChecker<ItpRefutation> {

	private final ItpSolver solver;
	private final Expr<? extends BoolType> init;
	private final Expr<? extends BoolType> target;

	private ExprTraceSeqItpChecker(final Expr<? extends BoolType> init, final Expr<? extends BoolType> target,
			final ItpSolver solver) {
		this.solver = checkNotNull(solver);
		this.init = checkNotNull(init);
		this.target = checkNotNull(target);
	}

	public static ExprTraceSeqItpChecker create(final Expr<? extends BoolType> init,
			final Expr<? extends BoolType> target, final ItpSolver solver) {
		return new ExprTraceSeqItpChecker(init, target, solver);
	}

	@Override
	public ExprTraceStatus<ItpRefutation> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		checkNotNull(trace);
		final int stateCount = trace.getStates().size();
		checkArgument(stateCount > 0);

		solver.push();
		final List<ItpMarker> markers = new ArrayList<>(stateCount + 1);
		for (int i = 0; i < stateCount + 1; ++i) {
			markers.add(solver.createMarker());
		}
		final ItpPattern pattern = solver.createSeqPattern(markers);

		final List<VarIndexing> indexings = new ArrayList<>(stateCount);
		indexings.add(VarIndexing.all(0));

		solver.add(markers.get(0), PathUtils.unfold(init, indexings.get(0)));
		solver.add(markers.get(0), PathUtils.unfold(trace.getState(0).toExpr(), indexings.get(0)));
		checkState(solver.check().isSat());

		for (int i = 1; i < stateCount; ++i) {
			indexings.add(indexings.get(i - 1).add(trace.getAction(i - 1).nextIndexing()));
			solver.add(markers.get(i), PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i)));
			solver.add(markers.get(i), PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1)));
		}

		solver.add(markers.get(trace.getStates().size()), PathUtils.unfold(target, indexings.get(stateCount - 1)));
		final boolean concretizable = solver.check().isSat();

		ExprTraceStatus<ItpRefutation> status = null;

		if (concretizable) {
			final Model model = solver.getModel();
			final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
			for (final VarIndexing indexing : indexings) {
				builder.add(PathUtils.extractValuation(model, indexing));
			}
			status = ExprTraceStatus.feasible(builder.build());
		} else {
			final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
			final Interpolant interpolant = solver.getInterpolant(pattern);
			for (int i = 0; i < markers.size() - 1; ++i) {
				interpolants.add(PathUtils.foldin(interpolant.eval(markers.get(i)), indexings.get(i)));
			}
			status = ExprTraceStatus.infeasible(ItpRefutation.sequence(interpolants));
		}

		solver.pop();

		assert status != null;
		return status;
	}

}
