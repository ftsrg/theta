package hu.bme.mit.theta.mcm.graph.classification.nodes;

import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.mcm.graph.classification.Thread;
import hu.bme.mit.theta.mcm.graph.classification.Variable;

public class Write extends Node {
    private static int cnt = 0;
    private final int id = cnt++;

    private final LitExpr<?> value;

    public Write(Thread parentThread, Variable var, LitExpr<?> value) {
        super(parentThread, var);
        this.value = value;
    }

    @Override
    public String toString() {
        return "W(" + getVar().toString() + ", " + value.toString() + ")_" + id;
    }
}
