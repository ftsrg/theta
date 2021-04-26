package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.analysis.stmtoptimizer.StmtSimplifier;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;

public class PredStmtOptimizer implements StmtOptimizer<PredState> {

	private PredStmtOptimizer(){}

	private static class LazyHolder {
		static final PredStmtOptimizer INSTANCE = new PredStmtOptimizer();
	}

	public static PredStmtOptimizer getInstance() {
		return PredStmtOptimizer.LazyHolder.INSTANCE;
	}

	@Override
	public Stmt optimizeStmt(final PredState state, final Stmt stmt){
		return StmtSimplifier.simplifyStmt(ImmutableValuation.empty(),stmt);
	}
}
