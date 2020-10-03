package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class TaggedNode<T extends MemoryAccess, L> extends Filter<T, L> {
    private final ForEachNode<T, L> supplier;

    public TaggedNode(ForEachNode<T, L> supplier) {
        this.supplier = supplier;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        return Set.of(GraphOrNodeSet.of(Set.of(supplier.getCurrentNode())));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        return null;
    }
}