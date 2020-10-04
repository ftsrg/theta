package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;

import java.util.Set;

public class Constraint<T> {
    private final Filter<T> filter;
    private final boolean checkAcyclic;
    private final boolean checkEmpty;
    private final boolean checkIrreflexive;

    public Constraint(Filter<T> filter, boolean checkAcyclic, boolean checkEmpty, boolean checkIrreflexive) {
        this.filter = filter;
        this.checkAcyclic = checkAcyclic;
        this.checkEmpty = checkEmpty;
        this.checkIrreflexive = checkIrreflexive;
    }

    public boolean checkMk(T source, T target, String label, boolean isFinal) {
        Set<GraphOrNodeSet<T>> resultSet = filter.filterMk(source, target, label, isFinal);
        for (GraphOrNodeSet<T> result : resultSet) {
            if(!check(result)) return false;
        }
        return true;
    }
    public boolean checkRm(T source, T target, String label) {
        Set<GraphOrNodeSet<T>> resultSet = filter.filterRm(source, target, label);
        for (GraphOrNodeSet<T> result : resultSet) {
            if(check(result)) return false;
        }
        return true;
    }

    private boolean check(GraphOrNodeSet<T> result) {
        if(checkAcyclic) {
            if(result.isGraph() && !result.getGraph().isAcyclic()) return false;
        }
        if(checkEmpty) {
            if(result.isGraph() && !result.getGraph().isEmpty() || !result.isGraph() && !result.getNodeSet().isEmpty()) return false;
        }
        if(checkIrreflexive) {
            if(result.isGraph() && !result.getGraph().isIrreflexive()) return false;
        }
        return true;
    }
}
