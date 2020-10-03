package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class Target<T extends MemoryAccess, L> extends Filter<T, L> {
    private final Filter<T, L> op;
    private Set<GraphOrNodeSet<T>> last;

    public Target(Filter<T, L> op) {
        this.op = op;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        Set<GraphOrNodeSet<T>> opSet = this.op.filterMk(source, target, label, isFinal);
        return getTargets(opSet);
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        Set<GraphOrNodeSet<T>> opSet = this.op.filterRm(source, target, label);
        return getTargets(opSet);
    }

    private Set<GraphOrNodeSet<T>> getTargets(Set<GraphOrNodeSet<T>> opSet) {
        boolean changed = false;
        for (GraphOrNodeSet<T> op : opSet) {
            if(op.isChanged()) {
                changed = true;
                op.setChanged(false);
            }
        }
        if(!changed) {
            return last;
        }
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (GraphOrNodeSet<T> op : opSet) {
            checkState(op.isGraph(), "Only graphs can have targets!");
            retSet.add(GraphOrNodeSet.of(op.getGraph().extractTargetNodes()));
        }
        return last = retSet;
    }
}
