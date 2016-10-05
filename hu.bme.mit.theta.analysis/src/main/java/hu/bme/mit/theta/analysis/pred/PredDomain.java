package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
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

		final Collection<Expr<? extends BoolType>> conjuncts = new ArrayList<>();
		for (final Expr<? extends BoolType> pred : state.getPreds()) {
			conjuncts.add(PathUtils.unfold(pred, 0));
		}
		solver.add(Not(And(conjuncts)));
		final boolean result = solver.check().isUnsat();

		solver.pop();
		return result;
	}

	@Override
	public boolean isBottom(final PredState state) {
		solver.push();

		for (final Expr<? extends BoolType> pred : state.getPreds()) {
			solver.add(PathUtils.unfold(pred, 0));
		}

		final boolean result = solver.check().isUnsat();

		solver.pop();
		return result;
	}

	@Override
	public boolean isLeq(final PredState state1, final PredState state2) {
		solver.push();

		for (final Expr<? extends BoolType> pred : state1.getPreds()) {
			solver.add(PathUtils.unfold(pred, 0));
		}

		final Collection<Expr<? extends BoolType>> unfoldedPreds = new ArrayList<>();
		for (final Expr<? extends BoolType> pred : state2.getPreds()) {
			unfoldedPreds.add(PathUtils.unfold(pred, 0));
		}
		solver.add(Not(And(unfoldedPreds)));

		final boolean isLeq = solver.check().isUnsat();
		solver.pop();
		return isLeq;
	}

}
