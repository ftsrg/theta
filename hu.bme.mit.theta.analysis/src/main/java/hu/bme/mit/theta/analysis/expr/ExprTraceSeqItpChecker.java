package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;

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

public class ExprTraceSeqItpChecker implements ExprTraceChecker<ItpRefutation> {

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
	public ExprTraceStatus2<ItpRefutation> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		checkNotNull(trace);

		final List<ItpMarker> markers = new ArrayList<>(trace.getStates().size() + 1);
		for (int i = 0; i < trace.getStates().size() + 1; ++i) {
			markers.add(solver.createMarker());
		}

		VarIndexing currentIndexing = VarIndexing.all(0);
		final List<VarIndexing> indexings = new ArrayList<>(trace.getStates().size());
		indexings.add(currentIndexing);

		final ItpPattern pattern = solver.createSeqPattern(markers);

		solver.push();
		solver.add(markers.get(0), PathUtils.unfold(init, currentIndexing));
		for (int i = 0; i < trace.getStates().size(); ++i) {
			solver.add(markers.get(i), PathUtils.unfold(trace.getState(i).toExpr(), currentIndexing));
			if (i < trace.getStates().size() - 1) {
				solver.add(markers.get(i + 1), PathUtils.unfold(trace.getAction(i).toExpr(), i));
				currentIndexing = currentIndexing.add(trace.getAction(i).nextIndexing());
				indexings.add(currentIndexing);
			}
		}
		solver.add(markers.get(trace.getStates().size()), PathUtils.unfold(target, currentIndexing));
		final boolean concretizable = solver.check().isSat();

		ExprTraceStatus2<ItpRefutation> status = null;

		if (concretizable) {
			final Model model = solver.getModel();
			final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
			for (final VarIndexing indexing : indexings) {
				builder.add(PathUtils.extractValuation(model, indexing));
			}
			return ExprTraceStatus2.feasible(builder.build());
		} else {
			final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
			final Interpolant interpolant = solver.getInterpolant(pattern);
			for (int i = 0; i < markers.size() - 1; ++i) {
				interpolants.add(PathUtils.foldin(interpolant.eval(markers.get(i)), indexings.get(i)));
			}
			status = ExprTraceStatus2.infeasible(ItpRefutation.sequence(interpolants));
		}

		solver.pop();

		assert status != null;
		return status;
	}

}
