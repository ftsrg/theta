package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public class ExplStmtAnalysis implements Analysis<ExplState, StmtAction, ExplPrec> {

	private final Domain<ExplState> domain;
	private final InitFunc<ExplState, ExplPrec> initFunc;
	private final TransferFunc<ExplState, StmtAction, ExplPrec> transferFunc;

	private ExplStmtAnalysis(final Solver solver, final Expr<BoolType> initExpr, final int maxStatesFromSolver) {
		checkNotNull(solver);
		checkNotNull(initExpr);
		this.domain = ExplDomain.getInstance();
		this.initFunc = ExplInitFunc.create(solver, initExpr);
		this.transferFunc = ExplStmtTransferFunc.create(solver, maxStatesFromSolver);
	}

	public static ExplStmtAnalysis create(final Solver solver, final Expr<BoolType> initExpr,
			final int maxStatesFromSolver) {
		return new ExplStmtAnalysis(solver, initExpr, maxStatesFromSolver);
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
	public TransferFunc<ExplState, StmtAction, ExplPrec> getTransferFunc() {
		return transferFunc;
	}

}
