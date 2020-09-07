package hu.bme.mit.theta.xcfa.analysis.stateless.graph.node;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.stateless.State;

public class Read extends Node{
    private final Valuation localVarsBefore;
    private final VarDecl<?> global;
    private final VarDecl<?> local;

    public Read(Valuation localVarsBefore, VarDecl<?> global, VarDecl<?> local,  Tuple2<XCFA.Process, XCFA.Process.Procedure.Edge> edge, int firstStmt) {
        super(edge.get1(), edge, firstStmt);
        this.localVarsBefore = localVarsBefore;
        this.global = global;
        this.local = local;
    }

    public Valuation getLocalVarsBefore() {
        return localVarsBefore;
    }

    public VarDecl<?> getGlobal() {
        return global;
    }

    @Override
    public void invalidate(State state) {
        super.invalidate(state);
        state.getMutablePartitionedValuation().clear(state.getPartitionId(getParentProcess()));
        state.getMutablePartitionedValuation().putAll(state.getPartitionId(getParentProcess()), getLocalVarsBefore());

    }

    @Override
    public Node duplicate() {
        return new Read(localVarsBefore, global, local, edgeBackup, firstStmtBackup);
    }

    public VarDecl<?> getLocal() {
        return local;
    }

    private static int cnt = 0;
    private final int id = cnt++;
    @Override
    public String toString() {
        return "R(" + getGlobal().getName() + ")_" + id;
    }
}
