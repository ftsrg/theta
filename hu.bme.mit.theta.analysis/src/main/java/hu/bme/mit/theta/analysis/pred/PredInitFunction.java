package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class PredInitFunction implements InitFunction<PredState, PredPrecision> {

	private final Solver solver;
	private final Expr<? extends BoolType> initExpr;

	private PredInitFunction(final Solver solver, final Expr<? extends BoolType> initExpr) {
		this.solver = checkNotNull(solver);
		this.initExpr = checkNotNull(initExpr);
	}

	public static PredInitFunction create(final Solver solver, final Expr<? extends BoolType> expr) {
		return new PredInitFunction(solver, expr);
	}

	@Override
	public Collection<? extends PredState> getInitStates(final PredPrecision precision) {
		checkNotNull(precision);
		return precision.createStates(solver, initExpr);
	}

}
