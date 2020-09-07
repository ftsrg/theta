package hu.bme.mit.theta.xcfa.analysis.stateless.graph.node;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;

public class Write extends Node {
    private final VarDecl<?> globalVar;
    private final LitExpr<?> value;

    public Write(VarDecl<?> globalVar, LitExpr<?> value) {
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
        return new Write(globalVar, value);
    }

    private static int cnt = 0;
    private final int id = cnt++;
    @Override
    public String toString() {
        return "\"W(" + getGlobalVar().getName() + ", " + getValue() + ")_" + id + "\"";
    }
}
