package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

/**
 * Utility for generating ExprStates.
 */
public final class ExprStates {

	private ExprStates() {
	}

	/**
	 * Generate all states that satisfy a given expression.
	 *
	 * @param solver Solver
	 * @param expr Expression to be satisfied
	 * @param exprIndex Index for unfolding the expression
	 * @param valuationToState Mapping from a valuation to a state
	 * @param stateIndexing Index for extracting the state
	 * @return States satisfying the expression
	 */
	public static <S extends ExprState> Collection<S> createStatesForExpr(final Solver solver,
			final Expr<BoolType> expr, final int exprIndex,
			final Function<? super Valuation, ? extends S> valuationToState, final VarIndexing stateIndexing) {
		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(PathUtils.unfold(expr, exprIndex));

			final Collection<S> result = new ArrayList<>();
			while (solver.check().isSat()) {
				final Model model = solver.getModel();
				final Valuation valuation = PathUtils.extractValuation(model, stateIndexing);
				final S state = valuationToState.apply(valuation);
				result.add(state);
				solver.add(Not(PathUtils.unfold(state.toExpr(), stateIndexing)));
			}
			return result;
		}
	}
}
