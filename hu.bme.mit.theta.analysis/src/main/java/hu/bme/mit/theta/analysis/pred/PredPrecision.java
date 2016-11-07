package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.solver.utils.SolverUtils.using;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.solver.Solver;

public interface PredPrecision extends Precision {

	public PredState createState(final Valuation valuation);

	public default Collection<? extends PredState> createStates(final Solver solver,
			final Expr<? extends BoolType> expr) {

		return using(solver, s -> {
			s.add(PathUtils.unfold(expr, 0));

			final Set<PredState> result = new HashSet<>();
			while (s.check().isSat()) {
				final Model model = s.getModel();
				final Valuation valuation = PathUtils.extractValuation(model, 0);
				final PredState state = createState(valuation);
				result.add(state);
				s.add(Not(model.toExpr()));
			}

			return result;
		});

	}
}
