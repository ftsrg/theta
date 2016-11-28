package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.utils.impl.PathUtils.extractValuation;
import static hu.bme.mit.theta.core.utils.impl.PathUtils.unfold;
import static hu.bme.mit.theta.solver.utils.SolverUtils.using;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;

public final class ExprStateUtils {

	private ExprStateUtils() {
	}

	public static Optional<Valuation> anyUncoveredSuccessor(final ExprState state, final ExprAction action,
			final Collection<? extends ExprState> succStates, final Solver solver) {
		return using(solver, s -> {
			final VarIndexing indexing = action.nextIndexing();
			s.add(unfold(state.toExpr(), 0));
			s.add(unfold(action.toExpr(), 0));
			for (final ExprState succState : succStates) {
				s.add(Not(unfold(succState.toExpr(), indexing)));
			}
			final SolverStatus status = s.check();

			if (status.isUnsat()) {
				return Optional.empty();
			} else if (status.isSat()) {
				final Model model = solver.getModel();
				final Valuation valuation = extractValuation(model, indexing);
				return Optional.of(valuation);
			} else {
				throw new AssertionError();
			}
		});
	}

	public static Optional<Valuation> anyUncoveredPredecessor(final Collection<? extends ExprState> predStates,
			final ExprAction action, final ExprState state, final Solver solver) {
		return using(solver, s -> {
			final VarIndexing indexing = action.nextIndexing();
			for (final ExprState predState : predStates) {
				s.add(Not(unfold(predState.toExpr(), 0)));
			}
			s.add(unfold(action.toExpr(), 0));
			s.add(unfold(state.toExpr(), indexing));
			final SolverStatus status = s.check();

			if (status.isUnsat()) {
				return Optional.empty();
			} else if (status.isSat()) {
				final Model model = solver.getModel();
				final Valuation valuation = extractValuation(model, 0);
				return Optional.of(valuation);
			} else {
				throw new AssertionError();
			}
		});
	}
}
