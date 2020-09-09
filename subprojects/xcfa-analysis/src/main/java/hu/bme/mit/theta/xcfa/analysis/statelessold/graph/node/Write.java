package hu.bme.mit.theta.xcfa.analysis.statelessold.graph.node;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.XCFA;

public class Write extends Node {
    private final VarDecl<?> globalVar;
    private final LitExpr<?> value;

    public Write(VarDecl<?> globalVar, LitExpr<?> value, XCFA.Process parentProcess) {
        super(parentProcess, null, 0);
        this.globalVar = globalVar;
        this.value = value;
    }

    public VarDecl<?> getGlobalVar() {
        return globalVar;
    }

    public LitExpr<?> getValue() {
        return value;
    }

    @Override
    public Node duplicate() {
        return new Write(globalVar, value, parentProcess);
    }

    private static int cnt = 0;
    private final int id = cnt++;
    @Override
    public String toString() {
        return "W(" + getGlobalVar().getName() + ", " + getValue() + ")_" + id;
    }
}
