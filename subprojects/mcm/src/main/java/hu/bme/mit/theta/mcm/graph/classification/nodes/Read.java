package hu.bme.mit.theta.mcm.graph.classification.nodes;

import hu.bme.mit.theta.mcm.graph.classification.Thread;
import hu.bme.mit.theta.mcm.graph.classification.Variable;

public class Read extends Node {
    private static int cnt = 0;
    private final int id = cnt++;
    public Read(Thread parentThread, Variable var) {
        super(parentThread, var);
    }

    @Override
    public String toString() {
        return "R(" + getVar().toString() + ")_" + id;
    }
}
