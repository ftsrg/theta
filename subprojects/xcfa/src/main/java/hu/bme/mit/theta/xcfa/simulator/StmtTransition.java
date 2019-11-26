package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;

/**
 * If an edge associated with a transition, this transition should be used.
 * An exception is LeaveTransition, which leaves a call.
 */
public class StmtTransition extends ProcessTransition {

	private Edge edge;

	public StmtTransition(XCFA.Process p, Edge edge) {
		super(p);
		this.edge = edge;
	}

	@Override
	public void step(RuntimeState state) throws ErrorReachedException {
		// TODO multiple stmts on an edge is not fully supported
		// some special stmt could mess up everything with multiple statements:
		// L0 -> L1 {
		//   call proc()
		//   a = a + 2
		// }
		// this code would try to call proc(), then increment a by 2, and *only then* proceed to the call itself.

		// Because of this, currently only one stmt/edge is enforced:
		Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
		for (Stmt stmt : edge.getStmts()) {
			CallState callState = state.getProcessState(process).getCallStackPeek();
			stmt.accept(StateUpdateVisitor.getInstance(), callState);
			callState.updateLocation(edge.getTarget());
		}
	}

	@Override
	public boolean enabled(RuntimeState state) {
		Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
		Stmt stmt = edge.getStmts().get(0);
		return stmt.accept(EnabledStmtVisitor.getInstance(), state);
	}
}
