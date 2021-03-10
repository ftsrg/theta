package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.StmtUnroller;
import hu.bme.mit.theta.analysis.expl.ExplStmtUnroller;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.List;

public class PredStmtUnroller implements StmtUnroller<PredState> {

	private PredStmtUnroller(){}

	private static class LazyHolder {
		static final PredStmtUnroller INSTANCE = new PredStmtUnroller();
	}

	public static PredStmtUnroller getInstance() {
		return PredStmtUnroller.LazyHolder.INSTANCE;
	}

	@Override
	public Stmt unrollStmt(final PredState state, final Stmt stmt) {
		return stmt;
	}
}
