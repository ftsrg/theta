package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.utils.impl.PathUtils.unfold;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.solver.Solver;

public final class ExprDomain implements Domain<ExprState> {

	private final Solver solver;

	public Valuation valuation;

	private ExprDomain(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static ExprDomain create(final Solver solver) {
		return new ExprDomain(solver);
	}

	@Override
	public boolean isTop(final ExprState state) {
		checkNotNull(state);

		solver.push();
		solver.add(Not(unfold(state.toExpr(), 0)));
		final boolean result = solver.check().isUnsat();
		solver.pop();
		return result;
	}

	@Override
	public boolean isBottom(final ExprState state) {
		checkNotNull(state);
		solver.push();
		solver.add(unfold(state.toExpr(), 0));
		final boolean result = solver.check().isUnsat();
		solver.pop();
		return result;
	}

	@Override
	public boolean isLeq(final ExprState state1, final ExprState state2) {
		checkNotNull(state1);
		checkNotNull(state2);

		solver.push();
		solver.add(unfold(state1.toExpr(), 0));
		solver.add(Not(unfold(state2.toExpr(), 0)));
		final boolean result = solver.check().isUnsat();
		if (!result) {
			final Model model = solver.getModel();
			valuation = PathUtils.extractValuation(model, 0);
		}
		solver.pop();
		return result;
	}

}
