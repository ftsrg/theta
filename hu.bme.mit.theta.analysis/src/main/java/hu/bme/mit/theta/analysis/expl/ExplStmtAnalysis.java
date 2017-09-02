package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public class ExplStmtAnalysis implements Analysis<ExplState, StmtAction, ExplPrec> {

	private final Domain<ExplState> domain;
	private final InitFunction<ExplState, ExplPrec> initFunction;
	private final TransferFunction<ExplState, StmtAction, ExplPrec> transferFunction;

	private ExplStmtAnalysis(final Solver solver, final Expr<BoolType> initExpr, final int maxStatesFromSolver) {
		checkNotNull(solver);
		checkNotNull(initExpr);
		this.domain = ExplDomain.getInstance();
		this.initFunction = ExplInitFunction.create(solver, initExpr);
		this.transferFunction = ExplStmtTransferFunction.create(solver, maxStatesFromSolver);
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
	public InitFunction<ExplState, ExplPrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ExplState, StmtAction, ExplPrec> getTransferFunction() {
		return transferFunction;
	}

}
