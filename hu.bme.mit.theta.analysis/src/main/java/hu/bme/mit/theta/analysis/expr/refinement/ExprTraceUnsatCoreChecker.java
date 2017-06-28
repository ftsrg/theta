package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.IndexedVars;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

/**
 * An ExprTraceChecker that generates an unsat core by checking the trace at
 * once.
 */
public final class ExprTraceUnsatCoreChecker implements ExprTraceChecker<VarsRefutation> {

	private final Solver solver;
	private final Expr<BoolType> init;
	private final Expr<BoolType> target;

	private ExprTraceUnsatCoreChecker(final Expr<BoolType> init, final Expr<BoolType> target, final Solver solver) {
		this.solver = checkNotNull(solver);
		this.init = checkNotNull(init);
		this.target = checkNotNull(target);
	}

	public static ExprTraceUnsatCoreChecker create(final Expr<BoolType> init, final Expr<BoolType> target,
			final Solver solver) {
		return new ExprTraceUnsatCoreChecker(init, target, solver);
	}

	@Override
	public ExprTraceStatus<VarsRefutation> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		checkNotNull(trace);
		final int stateCount = trace.getStates().size();

		final List<VarIndexing> indexings = new ArrayList<>(stateCount);
		indexings.add(VarIndexing.all(0));

		solver.push();

		solver.track(ExprUtils.getConjuncts(PathUtils.unfold(init, indexings.get(0))));
		solver.track(ExprUtils.getConjuncts(PathUtils.unfold(trace.getState(0).toExpr(), indexings.get(0))));
		assert solver.check().isSat() : "Initial state of the trace is not feasible";
		boolean concretizable = true;

		for (int i = 1; i < stateCount; ++i) {
			indexings.add(indexings.get(i - 1).add(trace.getAction(i - 1).nextIndexing()));
			solver.track(ExprUtils.getConjuncts(PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i))));
			solver.track(
					ExprUtils.getConjuncts(PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1))));

			if (!solver.check().isSat()) {
				concretizable = false;
				break;
			}
		}

		if (concretizable) {
			solver.track(ExprUtils.getConjuncts(PathUtils.unfold(target, indexings.get(stateCount - 1))));
			concretizable = solver.check().isSat();
		}

		ExprTraceStatus<VarsRefutation> status = null;

		if (concretizable) {
			final Model model = solver.getModel();
			final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
			for (final VarIndexing indexing : indexings) {
				builder.add(PathUtils.extractValuation(model, indexing));
			}
			status = ExprTraceStatus.feasible(Trace.of(builder.build(), trace.getActions()));
		} else {
			final Collection<Expr<BoolType>> unsatCore = solver.getUnsatCore();
			final IndexedVars indexedVars = ExprUtils.getVarsIndexed(unsatCore);
			status = ExprTraceStatus.infeasible(VarsRefutation.create(indexedVars));
		}
		assert status != null;
		solver.pop();

		return status;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
