package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class PredAnalysis implements Analysis<PredState, ExprAction, PredPrec> {

	private final Domain<PredState> domain;
	private final InitFunc<PredState, PredPrec> initFunc;
	private final TransferFunc<PredState, ExprAction, PredPrec> transferFunc;

	private PredAnalysis(final Solver solver, final Expr<BoolType> initExpr) {
		domain = PredDomain.create(solver);
		initFunc = PredInitFunc.create(solver, initExpr);
		transferFunc = PredTransferFunc.create(solver);
	}

	public static PredAnalysis create(final Solver solver, final Expr<BoolType> initExpr) {
		return new PredAnalysis(solver, initExpr);
	}

	////

	@Override
	public Domain<PredState> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<PredState, PredPrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<PredState, ExprAction, PredPrec> getTransferFunc() {
		return transferFunc;
	}

}
