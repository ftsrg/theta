package hu.bme.mit.theta.mcm.graph.classification.nodes;

import hu.bme.mit.theta.mcm.graph.classification.Thread;

public class Fence extends Node {
    private static int cnt = 0;
    private final int id = cnt++;

    public Fence(Thread parentThread) {
        super(parentThread, null);
    }

    @Override
    public String toString() {
        return "F_" + id;
    }
}
