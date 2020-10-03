package hu.bme.mit.theta.mcm;

import java.util.HashSet;
import java.util.Set;

public class MCM {

    private final Set<Graph> constraints;

    public MCM() {
        constraints = new HashSet<>();
    }

    public void addConstraint(Graph g) {
        constraints.add(g);
    }

    public Set<Graph> getConstraints() {
        return constraints;
    }
}
