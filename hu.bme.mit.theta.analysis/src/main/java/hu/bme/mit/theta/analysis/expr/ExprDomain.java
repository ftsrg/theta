package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.utils.PathUtils.unfold;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

public final class ExprDomain implements Domain<ExprState> {

	private final Solver solver;

	private ExprDomain(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static ExprDomain create(final Solver solver) {
		return new ExprDomain(solver);
	}

	@Override
	public boolean isTop(final ExprState state) {
		checkNotNull(state);

		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(Not(unfold(state.toExpr(), 0)));
			return solver.check().isUnsat();
		}
	}

	@Override
	public boolean isBottom(final ExprState state) {
		checkNotNull(state);
		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(unfold(state.toExpr(), 0));
			return solver.check().isUnsat();
		}
	}

	@Override
	public boolean isLeq(final ExprState state1, final ExprState state2) {
		checkNotNull(state1);
		checkNotNull(state2);

		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(unfold(state1.toExpr(), 0));
			solver.add(Not(unfold(state2.toExpr(), 0)));
			return solver.check().isUnsat();
		}
	}

}
