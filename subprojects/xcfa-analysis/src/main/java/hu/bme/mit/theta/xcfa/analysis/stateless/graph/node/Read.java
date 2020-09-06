package hu.bme.mit.theta.xcfa.analysis.stateless.graph.node;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.stateless.State;

public class Read extends Node{
    private final Valuation localVarsBefore;
    private final VarDecl<?> global;
    private final VarDecl<?> local;
    private final XCFA.Process parentProcess;

    public Read(Valuation localVarsBefore, VarDecl<?> global, VarDecl<?> local, XCFA.Process parentProcess) {
        this.localVarsBefore = localVarsBefore;
        this.global = global;
        this.parentProcess = parentProcess;
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
        state.getMutablePartitionedValuation().clear(state.getPartitionId(parentProcess));
        state.getMutablePartitionedValuation().putAll(state.getPartitionId(parentProcess), getLocalVarsBefore());

    }

    public XCFA.Process getParentProcess() {
        return parentProcess;
    }

    public VarDecl<?> getLocal() {
        return local;
    }
}
