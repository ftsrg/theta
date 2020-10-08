package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.XCFA;

class Write extends MemoryAccess implements hu.bme.mit.theta.mcm.graphfilter.interfaces.Write {
    private static int cnt;

    static {
        cnt = 0;
    }

    private final int id;
    private final LitExpr<?> value;

    Write(VarDecl<?> globalVar, LitExpr<?> value, XCFA.Process parentProcess, MemoryAccess lastNode) {
        super(globalVar, parentProcess, lastNode);
        this.value = value;
        id = cnt++;
    }

    LitExpr<?> getValue() {
        return value;
    }

    @Override
    public String toString() {
        return "\"W(" + getGlobalVariable().getName() + ", " + getValue() + ")_" + id + "\"";
    }
}
