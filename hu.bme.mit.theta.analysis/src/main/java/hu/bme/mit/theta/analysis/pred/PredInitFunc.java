package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

public final class PredInitFunc implements InitFunc<PredState, PredPrec> {

	private final Solver solver;
	private final Expr<BoolType> initExpr;

	private PredInitFunc(final Solver solver, final Expr<BoolType> initExpr) {
		this.solver = checkNotNull(solver);
		this.initExpr = checkNotNull(initExpr);
	}

	public static PredInitFunc create(final Solver solver, final Expr<BoolType> expr) {
		return new PredInitFunc(solver, expr);
	}

	@Override
	public Collection<? extends PredState> getInitStates(final PredPrec prec) {
		checkNotNull(prec);
		return ExprStates.createStatesForExpr(solver, initExpr, 0, prec::createState, VarIndexing.all(0));
	}

}
