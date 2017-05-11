package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.expr.Exprs.Not;
import static hu.bme.mit.theta.solver.utils.SolverUtils.using;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.solver.Solver;

public final class ExprStates {

	private ExprStates() {
	}

	public static <S extends ExprState> Collection<S> createStates(final Solver solver,
			final Expr<? extends BoolType> expr, final Function<? super Valuation, ? extends S> factory) {

		return using(solver, s -> {
			s.add(PathUtils.unfold(expr, 0));

			final Collection<S> result = new ArrayList<>();
			while (s.check().isSat()) {
				final Model model = s.getModel();
				final Valuation valuation = PathUtils.extractValuation(model, 0);
				final S state = factory.apply(valuation);
				result.add(state);
				s.add(Not(PathUtils.unfold(state.toExpr(), 0)));
			}

			return result;
		});
	}
}
