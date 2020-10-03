package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

public class SetMinus<T extends MemoryAccess, L> extends Filter<T, L> {
    private final Filter<T, L> lhs;
    private final Filter<T, L> rhs;
    private Set<GraphOrNodeSet<T>> last;

    public SetMinus(Filter<T, L> lhs, Filter<T, L> rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.last = null;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        Set<GraphOrNodeSet<T>> lhsSet = this.lhs.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet<T>> rhsSet = this.rhs.filterMk(source, target, label, isFinal);
        return getSets(lhsSet, rhsSet);
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        Set<GraphOrNodeSet<T>> lhsSet = this.lhs.filterRm(source, target, label);
        Set<GraphOrNodeSet<T>> rhsSet = this.rhs.filterRm(source, target, label);
        return getSets(lhsSet, rhsSet);
    }

    private Set<GraphOrNodeSet<T>> getSets(Set<GraphOrNodeSet<T>> lhsSet, Set<GraphOrNodeSet<T>> rhsSet) {
        boolean changed = false;
        for (GraphOrNodeSet<T> lhs : lhsSet) {
            if(lhs.isChanged()) {
                changed = true;
                lhs.setChanged(false);
            }
        }
        for (GraphOrNodeSet<T> rhs : rhsSet) {
            if(rhs.isChanged()) {
                changed = true;
                rhs.setChanged(false);
            }
        }
        if(!changed) {
            return last;
        }
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (GraphOrNodeSet<T> lhs : lhsSet) {
            for (GraphOrNodeSet<T> rhs : rhsSet) {
                retSet.add(getMinus(lhs, rhs));
            }
        }
        return last = retSet;
    }

    private GraphOrNodeSet<T> getMinus(GraphOrNodeSet<T> lhs, GraphOrNodeSet<T> rhs) {
        if (lhs.isGraph() && rhs.isGraph()) {
            return GraphOrNodeSet.of(lhs.getGraph().minus(rhs.getGraph()));
        } else if (!lhs.isGraph() && !rhs.isGraph()) {
            Set<T> lhsSet = new HashSet<>(lhs.getNodeSet());
            lhsSet.removeAll(rhs.getNodeSet());
            return GraphOrNodeSet.of(lhsSet);
        } else throw new UnsupportedOperationException("Cannot take the difference of nodes and a graph!");
    }
}

