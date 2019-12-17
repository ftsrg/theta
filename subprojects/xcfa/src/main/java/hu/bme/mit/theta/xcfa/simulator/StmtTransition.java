package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;

/**
 * A transition with an associated edge.
 * Almost every transition is alike, except LeaveTransition, at the moment.
 * Uses StmtExecutorInterface through EnabledStmtVisitor and StateUpdateVisitor to process statements.
 * An exception is LeaveTransition, which leaves a call.
 *
 * A transition instance should be independent of ExplStates.
 *
 * TODO cache already built transitions, add a wrapper to enable it :)
 * Note: In the future, to be able to cache these transitions, one should not store state of the explicit state in use.
 *
 * Note: Multiple statements on the same edge is not supported.
 *   Enabledness cannot be determined without running previous stmts
 *   Function calls will mess everything up
 */
public class StmtTransition extends ProcessTransition {

	private Edge edge;

	public StmtTransition(XCFA.Process p, Edge edge) {
		super(p);
		this.edge = edge;
	}

	@Override
	public void step(ExplState state) throws ErrorReachedException {
		// Multiple statements on the same edge is not supported, because:
		// some special stmt could mess up everything with multiple statements:
		// L0 -> L1 {
		//   call proc()
		//   a = a + 2
		// }
		// this code would try to call proc(), then increment a by 2, and *only then* proceed to the call itself.

		// also, enabledness is hard to determine

		// Because of this, currently only one stmt per edge is enforced:
		Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
		for (Stmt stmt : edge.getStmts()) {
			CallState callState = state.getProcessState(process).getCallStackPeek();
			stmt.accept(StateUpdateVisitor.getInstance(), callState);
			callState.updateLocation(edge.getTarget());
		}
	}

	@Override
	public boolean enabled(ExplState state) {
		Preconditions.checkState(edge.getStmts().size() == 1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
		Stmt stmt = edge.getStmts().get(0);
		CallState callState = state.getProcessState(process).getCallStackPeek();
		return stmt.accept(EnabledStmtVisitor.getInstance(), callState);
	}
}
