package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutablePartitionedValuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.List;
import java.util.Map;

abstract class MemoryAccess {
    protected final VarDecl<?> globalVar;
    private final XCFA.Process parentProcess;
    private final MemoryAccess lastNode;

    MemoryAccess(VarDecl<?> globalVar, XCFA.Process parentProcess, MemoryAccess lastNode) {
        this.globalVar = globalVar;
        this.parentProcess = parentProcess;
        this.lastNode = lastNode;
    }

    VarDecl<?> getGlobalVar() {
        return globalVar;
    }

    XCFA.Process getParentProcess() {
        return parentProcess;
    }

    boolean revert(Map<XCFA.Process, List<StackFrame>> stackFrames, Map<XCFA.Process, MemoryAccess> lastNodes, MutablePartitionedValuation mutablePartitionedValuation, int partitionId) {
        lastNodes.put(parentProcess, lastNode);
        return false;
    }
}
