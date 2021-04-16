package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.stmt.Stmt;

public class XstsStmtOptimizer<S extends ExprState> implements StmtOptimizer<XstsState<S>> {

	private final StmtOptimizer<S> stmtOptimizer;

	private XstsStmtOptimizer(final StmtOptimizer<S> stmtOptimizer) {
		this.stmtOptimizer = stmtOptimizer;
	}

	public static <S extends ExprState> XstsStmtOptimizer<S> create(final StmtOptimizer<S> stmtOptimizer){
		return new XstsStmtOptimizer<>(stmtOptimizer);
	}

	@Override
	public Stmt optimizeStmt(final XstsState<S> state, final Stmt stmt) {
		return stmtOptimizer.optimizeStmt(state.getState(),stmt);
	}
}
