package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.solver.Solver;

public final class PredDomain implements Domain<PredState> {

	private final Solver solver;

	public static PredDomain create(final Solver solver) {
		return new PredDomain(solver);
	}

	private PredDomain(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public boolean isTop(final PredState state) {
		solver.push();
		solver.add(PathUtils.unfold(Not(state.toExpr()), 0));
		final boolean result = solver.check().isUnsat();
		solver.pop();
		return result;
	}

	@Override
	public boolean isBottom(final PredState state) {
		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		final boolean result = solver.check().isUnsat();
		solver.pop();
		return result;
	}

	@Override
	public boolean isLeq(final PredState state1, final PredState state2) {
		solver.push();
		solver.add(PathUtils.unfold(state1.toExpr(), 0));
		solver.add(PathUtils.unfold(Not(state2.toExpr()), 0));
		final boolean isLeq = solver.check().isUnsat();
		solver.pop();
		return isLeq;
	}

}
