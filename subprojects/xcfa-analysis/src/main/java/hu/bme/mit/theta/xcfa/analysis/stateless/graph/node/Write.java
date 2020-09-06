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
}
