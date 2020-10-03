package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

public class Multiply<T extends MemoryAccess, L> extends Filter<T, L> {
    private final Filter<T, L> lhs;
    private final Filter<T, L> rhs;
    private Set<GraphOrNodeSet<T>> last;

    public Multiply(Filter<T, L> lhs, Filter<T, L> rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.last = null;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {

        Set<GraphOrNodeSet<T>> lhs = this.lhs.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet<T>> rhs = this.rhs.filterMk(source, target, label, isFinal);
        return getMultiplication(lhs, rhs);
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        Set<GraphOrNodeSet<T>> lhs = this.lhs.filterRm(source, target, label);
        Set<GraphOrNodeSet<T>> rhs = this.rhs.filterRm(source, target, label);
        return getMultiplication(lhs, rhs);
    }

    private Set<GraphOrNodeSet<T>> getMultiplication(Set<GraphOrNodeSet<T>> lhsSet, Set<GraphOrNodeSet<T>> rhsSet) {
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
                if(lhs.isGraph() || rhs.isGraph()) {
                    throw new UnsupportedOperationException("Cannot multiply graphs!");
                }
                else {
                    Graph<T> ret = Graph.create(false);
                    for (T t : lhs.getNodeSet()) {
                        for (T t1 : rhs.getNodeSet()) {
                            ret.addEdge(t, t1, false);
                        }
                    }
                    retSet.add(GraphOrNodeSet.of(ret));
                }
            }
        }
        return last = retSet;

    }

}
