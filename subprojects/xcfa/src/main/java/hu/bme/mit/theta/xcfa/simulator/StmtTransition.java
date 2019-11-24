package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure.Edge;

public class StmtTransition extends ProcessTransition {

    private Edge edge;

    StmtTransition(ProcessState p, Edge edge) {
        super(p);
        this.edge = edge;
    }

    @Override
    public void step() {
        // TODO multiple stmts on an edge is not fully supported
        // some special stmt could mess up everything with multiple statements:
        // L0 -> L1 {
        //   call proc()
        //   a = a + 2
        // }
        // this code would try to call proc(), then increment a by 2, and *only then* proceed to the call itself.

        // Because of this, currently only one stmt/edge is enforced:
        Preconditions.checkState(edge.getStmts().size()==1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
        for (Stmt stmt : edge.getStmts()) {
            CallState x = processState.callStack.peek();
            stmt.accept(StateUpdateVisitor.getInstance(), x);
            x.currentLocation = edge.getTarget();

            // TODO Rework: now as the Simulator is not part of the test suite, getting to the error location is not an error
            // test that the procedure did not get to the error location
            Preconditions.checkState(x.currentLocation != x.procedure.getErrorLoc(), "Test failed: Reached error location.");
            // step succeeded
        }
    }

    @Override
    public boolean enabled(RuntimeState state) {
        Preconditions.checkState(edge.getStmts().size()==1, "Only 1 stmt is supported / edge. Should work in non-special cases, but remove with care!");
        for (Stmt stmt : edge.getStmts()) {
            if (stmt.accept(EnabledTransitionVisitor.getInstance(), state)) {
                return true;
            }
        }
        return false;
    }
}
