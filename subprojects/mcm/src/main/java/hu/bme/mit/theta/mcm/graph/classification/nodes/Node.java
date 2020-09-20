package hu.bme.mit.theta.mcm.graph.classification.nodes;

import hu.bme.mit.theta.mcm.graph.classification.Thread;
import hu.bme.mit.theta.mcm.graph.classification.Variable;

public abstract class Node {
    private final Thread parentThread;
    private final Variable var;

    protected Node(Thread parentThread, Variable var) {
        this.parentThread = parentThread;
        this.var = var;
    }

    public Thread getParentThread() {
        return parentThread;
    }

    public Variable getVar() {
        return var;
    }
}
