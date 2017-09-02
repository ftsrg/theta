package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class ExplAnalysis implements Analysis<ExplState, ExprAction, ExplPrec> {

	private final Domain<ExplState> domain;
	private final InitFunction<ExplState, ExplPrec> initFunction;
	private final TransferFunction<ExplState, ExprAction, ExplPrec> transferFunction;

	private ExplAnalysis(final Solver solver, final Expr<BoolType> initExpr) {
		checkNotNull(solver);
		checkNotNull(initExpr);
		this.domain = ExplDomain.getInstance();
		this.initFunction = ExplInitFunction.create(solver, initExpr);
		this.transferFunction = ExplTransferFunction.create(solver);

	}

	public static ExplAnalysis create(final Solver solver, final Expr<BoolType> initExpr) {
		return new ExplAnalysis(solver, initExpr);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<ExplState, ExplPrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ExplState, ExprAction, ExplPrec> getTransferFunction() {
		return transferFunction;
	}

}
