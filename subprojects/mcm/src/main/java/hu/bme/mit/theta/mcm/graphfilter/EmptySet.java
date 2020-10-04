package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class EmptySet<T extends MemoryAccess> extends Filter<T> {
    private final Set<GraphOrNodeSet<T>> emptySet = Set.of(GraphOrNodeSet.of(Graph.create(false)));
    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        return emptySet;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        return emptySet;
    }
}
