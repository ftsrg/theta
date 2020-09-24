package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graph.EdgeDB;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Predicate;

public class MCM {

    private final Set<EdgeDBWrapper> constraints;

    public MCM() {
        constraints = new HashSet<>();
    }

    public void addPredicate(Predicate<EdgeDB> predicate, Set<String> modifications) {
        constraints.add(new EdgeDBWrapper(EdgeDB.empty(), modifications, predicate));
    }

    public Set<EdgeDBWrapper> getConstraints() {
        return constraints;
    }
}
