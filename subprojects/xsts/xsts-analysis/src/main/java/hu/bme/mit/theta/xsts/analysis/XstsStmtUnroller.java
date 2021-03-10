package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.StmtUnroller;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.stmt.Stmt;

public class XstsStmtUnroller<S extends ExprState> implements StmtUnroller<XstsState<S>> {

	private final StmtUnroller<S> stmtUnroller;

	private XstsStmtUnroller(final StmtUnroller<S> stmtUnroller) {
		this.stmtUnroller = stmtUnroller;
	}

	public static <S extends ExprState> XstsStmtUnroller<S> create(final StmtUnroller<S> stmtUnroller){
		return new XstsStmtUnroller<>(stmtUnroller);
	}

	@Override
	public Stmt unrollStmt(final XstsState<S> state, final Stmt stmt) {
		return stmtUnroller.unrollStmt(state.getState(),stmt);
	}
}
