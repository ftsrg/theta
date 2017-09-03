package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

public final class ExplInitFunc implements InitFunc<ExplState, ExplPrec> {

	private final Solver solver;
	private final Expr<BoolType> initExpr;

	private ExplInitFunc(final Solver solver, final Expr<BoolType> initExpr) {
		this.solver = checkNotNull(solver);
		this.initExpr = checkNotNull(initExpr);
	}

	public static ExplInitFunc create(final Solver solver, final Expr<BoolType> initExpr) {
		return new ExplInitFunc(solver, initExpr);
	}

	@Override
	public Collection<? extends ExplState> getInitStates(final ExplPrec prec) {
		checkNotNull(prec);
		return ExprStates.createStatesForExpr(solver, initExpr, 0, prec::createState, VarIndexing.all(0));
	}

}
