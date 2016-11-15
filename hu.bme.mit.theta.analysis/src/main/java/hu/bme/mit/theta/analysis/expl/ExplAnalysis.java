package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.LTS;
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
	private final LTS<? super ExplState, ? extends ExprAction> actionFunction;

	private ExplAnalysis(final Solver solver, final Expr<? extends BoolType> initExpr,
			final LTS<? super ExplState, ? extends ExprAction> actionFunction) {
		checkNotNull(solver);
		checkNotNull(initExpr);
		this.domain = ExplDomain.getInstance();
		this.initFunction = ExplInitFunction.create(solver, initExpr);
		this.transferFunction = ExplTransferFunction.create(solver);
		this.actionFunction = checkNotNull(actionFunction);

	}

	public static ExplAnalysis create(final Solver solver, final Expr<? extends BoolType> initExpr,
			final LTS<? super ExplState, ? extends ExprAction> actionFunction) {
		return new ExplAnalysis(solver, initExpr, actionFunction);
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

	@Override
	public LTS<? super ExplState, ? extends ExprAction> getActionFunction() {
		return actionFunction;
	}

}
