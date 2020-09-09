package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.XCFA;

class Write extends MemoryAccess {
    private final LitExpr<?> value;

    Write(VarDecl<?> globalVar, LitExpr<?> value, XCFA.Process parentProcess) {
        super(globalVar, parentProcess);
        this.value = value;
    }

    LitExpr<?> getValue() {
        return value;
    }
}
