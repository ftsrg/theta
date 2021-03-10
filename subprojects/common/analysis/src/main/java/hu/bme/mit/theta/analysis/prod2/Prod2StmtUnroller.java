package hu.bme.mit.theta.analysis.prod2;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.StmtUnroller;
import hu.bme.mit.theta.core.stmt.Stmt;

public class Prod2StmtUnroller<S1 extends State, S2 extends State> implements StmtUnroller<Prod2State<S1,S2>> {

	private final StmtUnroller<S1> stmtUnroller1;
	private final StmtUnroller<S2> stmtUnroller2;

	private Prod2StmtUnroller(final StmtUnroller<S1> stmtUnroller1, final StmtUnroller<S2> stmtUnroller2) {
		this.stmtUnroller1 = stmtUnroller1;
		this.stmtUnroller2 = stmtUnroller2;
	}

	public static <S1 extends State, S2 extends State, A extends Action> Prod2StmtUnroller<S1,S2> create(final StmtUnroller<S1> stmtUnroller1,
																										   final StmtUnroller<S2> stmtUnroller2){
		return new Prod2StmtUnroller<>(stmtUnroller1,stmtUnroller2);
	}

	@Override
	public Stmt unrollStmt(final Prod2State<S1, S2> state, final Stmt stmt) {
		return stmtUnroller2.unrollStmt(state.getState2(),stmtUnroller1.unrollStmt(state.getState1(),stmt));
	}
}
