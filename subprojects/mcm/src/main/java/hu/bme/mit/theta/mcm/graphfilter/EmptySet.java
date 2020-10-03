package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class EmptySet<T extends MemoryAccess, L> extends Filter<T, L> {
    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        return Set.of(GraphOrNodeSet.of(Graph.create(false)));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        return Set.of(GraphOrNodeSet.of(Graph.create(false)));
    }
}
