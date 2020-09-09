package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.List;

class Read extends MemoryAccess {
    private final VarDecl<?> localVar;

    private final Valuation savedState;
    private final List<StackFrame> savedStack;

    private final List<Read> precedingReads;

    Read(VarDecl<?> globalVar, VarDecl<?> localVar, List<StackFrame> savedStack, Read lastRead, XCFA.Process parentProcess) {
        super(globalVar, parentProcess);
        this.localVar = localVar;
        this.savedStack = savedStack;
        savedState = null;
        if (lastRead == null) {
            precedingReads = new ArrayList<>();
        }
        else {
            precedingReads = new ArrayList<>(lastRead.precedingReads);
            precedingReads.add(lastRead);
        }
    }

    VarDecl<?> getLocalVar() {
        return localVar;
    }
}
