package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;

public class StmtTransitionImpl extends StmtTransition{
    private final ProcedureData.EdgeWrapper edge;

    public StmtTransitionImpl(XCFA.Process p, ProcedureData.EdgeWrapper edge) {
        super(p);
        this.edge = edge;
    }

    @Override
    public void execute(ExplState state) {
        // Multiple statements on the same edge is not supported, because:
        // some special stmt could mess up everything with multiple statements:
        // L0 -> L1 {
        //   call proc()
        //   a = a + 2
        // }
        // this code would try to call proc(), then increment a by 2, and *only then* proceed to the call itself.

        // also, enabledness is hard to determine

        // Because of this, currently only one stmt per edge is enforced:

        CallState callState = state.getProcessState(getProcess()).getCallStackPeek();
        edge.getStmt().accept(StateUpdateVisitor.getInstance(), callState);
        callState.updateLocation(edge.getTarget());
    }

    @Override
    public boolean enabled(ExplState state) {
        Stmt stmt = edge.getStmt();
        CallState callState = state.getProcessState(getProcess()).getCallStackPeek();
        return stmt.accept(EnabledStmtVisitor.getInstance(), callState);
    }

    // read vars that don't change
    public Collection<VarDecl<?>> getRWVars() {
        return StmtUtils.getVars(edge.getStmt());
    }

    // read vars that do change
    public Collection<VarDecl<?>> getWVars() {
        return StmtUtils.getWrittenVars(edge.getStmt());
    }

    @Override
    public String toString() {
        return edge.getStmt().toString();
    }
}
