package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graph.EdgeDB;

import java.util.function.Predicate;

public class MCM {

    private Predicate<EdgeDB> constraints;

    public boolean checkConformity(EdgeDB edgeDataBase) {
        return constraints == null || constraints.test(edgeDataBase);
    }

    public void addPredicate(Predicate<EdgeDB> newPredicate) {
        constraints = constraints == null ? newPredicate : newPredicate.and(constraints);
    }
}
