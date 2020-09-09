package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.XCFA;

abstract class MemoryAccess {
    protected final VarDecl<?> globalVar;
    private final XCFA.Process parentProcess;

    MemoryAccess(VarDecl<?> globalVar, XCFA.Process parentProcess) {
        this.globalVar = globalVar;
        this.parentProcess = parentProcess;
    }

    VarDecl<?> getGlobalVar() {
        return globalVar;
    }

    XCFA.Process getParentProcess() {
        return parentProcess;
    }
}
