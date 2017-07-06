package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;

/**
 * An ExprTraceChecker that generates a binary interpolant by incrementally
 * checking the counterexample backward.
 */
public class ExprTraceBwBinItpChecker implements ExprTraceChecker<ItpRefutation> {

	private final ItpSolver solver;
	private final Expr<BoolType> init;
	private final Expr<BoolType> target;

	private ExprTraceBwBinItpChecker(final Expr<BoolType> init, final Expr<BoolType> target, final ItpSolver solver) {
		this.solver = checkNotNull(solver);
		this.init = checkNotNull(init);
		this.target = checkNotNull(target);
	}

	public static ExprTraceBwBinItpChecker create(final Expr<BoolType> init, final Expr<BoolType> target,
			final ItpSolver solver) {
		return new ExprTraceBwBinItpChecker(init, target, solver);
	}

	@Override
	public ExprTraceStatus<ItpRefutation> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		checkNotNull(trace);
		final Trace<? extends ExprState, ? extends ExprAction> traceRev = trace.reverse();
		final int stateCount = trace.getStates().size();

		final List<VarIndexing> indexings = new ArrayList<>(stateCount);
		indexings.add(VarIndexing.all(10 * stateCount));

		solver.push();

		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		int nPush = 1;
		solver.add(A, PathUtils.unfold(target, indexings.get(0)));
		solver.add(A, PathUtils.unfold(traceRev.getState(0).toExpr(), indexings.get(0)));
		assert solver.check().isSat() : "Initial state of the trace is not feasible";
		int satPostfix = 0;

		for (int i = 1; i < stateCount; ++i) {
			solver.push();
			++nPush;
			indexings.add(indexings.get(i - 1).sub(traceRev.getAction(i - 1).nextIndexing()));
			solver.add(A, PathUtils.unfold(traceRev.getState(i).toExpr(), indexings.get(i)));
			solver.add(A, PathUtils.unfold(traceRev.getAction(i - 1).toExpr(), indexings.get(i)));

			if (solver.check().isSat()) {
				satPostfix = i;
			} else {
				solver.pop();
				--nPush;
				break;
			}
		}

		final boolean concretizable;

		if (satPostfix == stateCount - 1) {
			solver.add(B, PathUtils.unfold(init, indexings.get(stateCount - 1)));
			concretizable = solver.check().isSat();
		} else {
			solver.add(B, PathUtils.unfold(traceRev.getState(satPostfix + 1).toExpr(), indexings.get(satPostfix + 1)));
			solver.add(B, PathUtils.unfold(traceRev.getAction(satPostfix).toExpr(), indexings.get(satPostfix + 1)));
			solver.check();
			assert solver.getStatus().isUnsat() : "Trying to interpolate a feasible formula";
			concretizable = false;
		}

		ExprTraceStatus<ItpRefutation> status = null;
		if (concretizable) {
			final Model model = solver.getModel();
			final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
			for (final VarIndexing indexing : indexings) {
				builder.add(PathUtils.extractValuation(model, indexing));
			}
			status = ExprTraceStatus.feasible(Trace.of(builder.build().reverse(), trace.getActions()));
		} else {
			final Interpolant interpolant = solver.getInterpolant(pattern);
			final Expr<BoolType> itpFolded = PathUtils.foldin(interpolant.eval(A), indexings.get(satPostfix));
			status = ExprTraceStatus
					.infeasible(ItpRefutation.binary(itpFolded, stateCount - 1 - satPostfix, stateCount));
		}
		assert status != null;
		solver.pop(nPush);

		return status;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
