package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;

import java.util.Set;

public abstract class Filter<T, L> {
    public abstract Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal);
    public abstract Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label);
}
