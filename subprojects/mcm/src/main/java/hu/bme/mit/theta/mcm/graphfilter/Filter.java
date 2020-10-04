package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;

import java.util.Set;

public abstract class Filter<T> {
    public abstract Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal);
    public abstract Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label);
}
