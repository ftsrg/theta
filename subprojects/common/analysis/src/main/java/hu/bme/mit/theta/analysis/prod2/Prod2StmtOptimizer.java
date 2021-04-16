package hu.bme.mit.theta.analysis.prod2;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.core.stmt.Stmt;

public class Prod2StmtOptimizer<S1 extends State, S2 extends State> implements StmtOptimizer<Prod2State<S1,S2>> {

	private final StmtOptimizer<S1> stmtOptimizer1;
	private final StmtOptimizer<S2> stmtOptimizer2;

	private Prod2StmtOptimizer(final StmtOptimizer<S1> stmtOptimizer1, final StmtOptimizer<S2> stmtOptimizer2) {
		this.stmtOptimizer1 = stmtOptimizer1;
		this.stmtOptimizer2 = stmtOptimizer2;
	}

	public static <S1 extends State, S2 extends State, A extends Action> Prod2StmtOptimizer<S1,S2> create(final StmtOptimizer<S1> stmtOptimizer1,
																										   final StmtOptimizer<S2> stmtOptimizer2){
		return new Prod2StmtOptimizer<>(stmtOptimizer1,stmtOptimizer2);
	}

	@Override
	public Stmt optimizeStmt(final Prod2State<S1, S2> state, final Stmt stmt) {
		return stmtOptimizer2.optimizeStmt(state.getState2(),stmtOptimizer1.optimizeStmt(state.getState1(),stmt));
	}
}
