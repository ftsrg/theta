package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class ExplInitFunction implements InitFunction<ExplState, ExplPrec> {

	private final Solver solver;
	private final Expr<? extends BoolType> initExpr;

	private ExplInitFunction(final Solver solver, final Expr<? extends BoolType> initExpr) {
		this.solver = checkNotNull(solver);
		this.initExpr = checkNotNull(initExpr);
	}

	public static ExplInitFunction create(final Solver solver, final Expr<? extends BoolType> initExpr) {
		return new ExplInitFunction(solver, initExpr);
	}

	@Override
	public Collection<? extends ExplState> getInitStates(final ExplPrec precision) {
		checkNotNull(precision);
		return precision.createStates(solver, initExpr);
	}

}
