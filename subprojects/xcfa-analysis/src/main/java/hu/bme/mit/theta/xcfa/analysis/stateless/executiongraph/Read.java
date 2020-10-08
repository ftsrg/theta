package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutablePartitionedValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

class Read extends MemoryAccess implements hu.bme.mit.theta.mcm.graphfilter.interfaces.Read {
    private static int cnt;

    static {
        cnt = 0;
    }

    private final int id;
    private final VarDecl<?> localVar;

    private final Valuation savedState;
    private final List<StackFrame> savedStack;
    private final boolean savedAtomicity;

    private final List<Read> precedingReads;

    Read(VarDecl<?> globalVar, VarDecl<?> localVar, Valuation savedState, List<StackFrame> savedStack, Read lastRead, XCFA.Process parentProcess, boolean atomic, MemoryAccess lastNode) {
        super(globalVar, parentProcess, lastNode);
        this.localVar = localVar;
        this.savedStack = new ArrayList<>();
        savedStack.forEach(stackFrame -> this.savedStack.add(stackFrame.duplicate()));
        this.savedState = savedState;
        if (lastRead == null) {
            precedingReads = new ArrayList<>();
        }
        else {
            precedingReads = new ArrayList<>(lastRead.precedingReads);
            precedingReads.add(lastRead);
        }
        this.savedAtomicity = atomic;
        id = cnt++;
    }

    VarDecl<?> getLocalVar() {
        return localVar;
    }

    List<Read> getPrecedingReads() {
        return precedingReads;
    }

    @Override
    boolean revert(Map<XCFA.Process, List<StackFrame>> stackFrames, Map<XCFA.Process, MemoryAccess> lastNode, MutablePartitionedValuation mutablePartitionedValuation, int partitionId) {
        super.revert(stackFrames, lastNode, mutablePartitionedValuation, partitionId);
        ArrayList<StackFrame> stackCopy = new ArrayList<>();
        savedStack.forEach(stackFrame -> stackCopy.add(stackFrame.duplicate()));
        stackFrames.put(getProcess(), stackCopy);
        mutablePartitionedValuation.clear(partitionId);
        mutablePartitionedValuation.putAll(partitionId, savedState);
        return savedAtomicity;
    }

    @Override
    public String toString() {
        return "\"R(" + getGlobalVariable().getName() + ")_" + id + "\"";
    }
}
