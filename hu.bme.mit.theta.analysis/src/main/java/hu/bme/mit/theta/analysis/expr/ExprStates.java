package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.solver.utils.SolverUtils.using;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;

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
	 * @param stateIndex Index for extracting the state
	 * @return States satisfying the expression
	 */
	public static <S extends ExprState> Collection<S> createStatesForExpr(
			final Solver solver, final Expr<BoolType> expr, final int exprIndex,
			final Function<? super Valuation, ? extends S> valuationToState,
			final int stateIndex) {

		return using(solver, s -> {
			s.add(PathUtils.unfold(expr, exprIndex));

			final Collection<S> result = new ArrayList<>();
			while (s.check().isSat()) {
				final Model model = s.getModel();
				final Valuation valuation = PathUtils.extractValuation(model,
						stateIndex);
				final S state = valuationToState.apply(valuation);
				result.add(state);
				s.add(Not(PathUtils.unfold(state.toExpr(), stateIndex)));
			}

			return result;
		});
	}
}
