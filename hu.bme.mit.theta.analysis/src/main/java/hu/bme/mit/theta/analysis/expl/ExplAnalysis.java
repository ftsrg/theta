package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class ExplAnalysis implements Analysis<ExplState, ExprAction, ExplPrecision> {

	private final Domain<ExplState> domain;
	private final InitFunction<ExplState, ExplPrecision> initFunction;
	private final TransferFunction<ExplState, ExprAction, ExplPrecision> transferFunction;

	private ExplAnalysis(final Solver solver, final Expr<? extends BoolType> initExpr) {
		checkNotNull(solver);
		checkNotNull(initExpr);
		this.domain = ExplDomain.getInstance();
		this.initFunction = ExplInitFunction.create(solver, initExpr);
		this.transferFunction = ExplTransferFunction.create(solver);

	}

	public static ExplAnalysis create(final Solver solver, final Expr<? extends BoolType> initExpr) {
		return new ExplAnalysis(solver, initExpr);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<ExplState, ExplPrecision> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ExplState, ExprAction, ExplPrecision> getTransferFunction() {
		return transferFunction;
	}

}
