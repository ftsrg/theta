package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graph.EdgeDB;

import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

public class MCM {

    private Predicate<EdgeDB> constraints;
    private final Map<String, UnaryOperator<List<EdgeDB>>> definitions;

    public MCM(Map<String, UnaryOperator<List<EdgeDB>>> definitions) {
        this.definitions = definitions;
    }

    public boolean checkConformity(EdgeDB edgeDataBase) {
        return constraints == null || constraints.test(edgeDataBase);
    }

    public void addPredicate(Predicate<EdgeDB> newPredicate) {
        constraints = constraints == null ? newPredicate : newPredicate.and(constraints);
    }

    public Map<String, UnaryOperator<List<EdgeDB>>> getDefinitions() {
        return definitions;
    }
}
