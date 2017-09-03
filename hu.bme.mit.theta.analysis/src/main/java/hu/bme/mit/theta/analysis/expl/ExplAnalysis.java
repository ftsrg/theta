package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class ExplAnalysis implements Analysis<ExplState, ExprAction, ExplPrec> {

	private final Domain<ExplState> domain;
	private final InitFunc<ExplState, ExplPrec> initFunc;
	private final TransferFunc<ExplState, ExprAction, ExplPrec> transferFunc;

	private ExplAnalysis(final Solver solver, final Expr<BoolType> initExpr) {
		checkNotNull(solver);
		checkNotNull(initExpr);
		this.domain = ExplDomain.getInstance();
		this.initFunc = ExplInitFunc.create(solver, initExpr);
		this.transferFunc = ExplTransferFunc.create(solver);

	}

	public static ExplAnalysis create(final Solver solver, final Expr<BoolType> initExpr) {
		return new ExplAnalysis(solver, initExpr);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<ExplState, ExplPrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<ExplState, ExprAction, ExplPrec> getTransferFunc() {
		return transferFunc;
	}

}
