package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class NodeTag<T extends MemoryAccess> extends Filter<T> {
    private final ForEachNode<T> supplier;

    public NodeTag(ForEachNode<T> supplier) {
        this.supplier = supplier;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        return Set.of(GraphOrNodeSet.of(Set.of(supplier.getCurrentNode())));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        return null;
    }
}