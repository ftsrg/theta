package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class Tagged<T extends MemoryAccess> extends Filter<T> {
    private final Set<Filter<T>> tags;
    private final Filter<T> named;
    private Set<GraphOrNodeSet<T>> last;

    public Tagged(Set<Filter<T>> tags, Filter<T> named) {
        this.tags = tags;
        this.named = named;
        this.last = null;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        Set<GraphOrNodeSet<T>> baseSet = named.filterMk(source, target, label, isFinal);
        checkState(baseSet.size() == 1, "Tagged expression cannot handle more than one nodeset from its named expression!");
        GraphOrNodeSet<T> base = baseSet.iterator().next();
        Set<GraphOrNodeSet<T>> constraints = new HashSet<>();
        for (Filter<T> tag : tags) {
            constraints.addAll(tag.filterMk(source, target, label, isFinal));
        }
        return getTagged(base, constraints);
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        Set<GraphOrNodeSet<T>> baseSet = named.filterRm(source, target, label);
        checkState(baseSet.size() == 1, "Tagged expression cannot handle more than one nodeset from its named expression!");
        GraphOrNodeSet<T> base = baseSet.iterator().next();
        Set<GraphOrNodeSet<T>> constraints = new HashSet<>();
        for (Filter<T> tag : tags) {
            constraints.addAll(tag.filterRm(source, target, label));
        }
        return getTagged(base, constraints);
    }

    private Set<GraphOrNodeSet<T>> getTagged(GraphOrNodeSet<T> base, Set<GraphOrNodeSet<T>> constraints) {
        boolean changed = false;
        checkState(!base.isGraph(), "Cannot filter graphs!");
        if(base.isChanged()) {
            changed = true;
            base.setChanged(false);
        }
        for (GraphOrNodeSet<T> constraint : constraints) {
            checkState(!constraint.isGraph(), "Cannot filter graphs!");
            if(constraint.isChanged()) {
                changed = true;
                constraint.setChanged(false);
            }
        }
        if(!changed) {
            return last;
        }
        else {
            Set<T> retSet = new HashSet<>();
            for (T t : base.getNodeSet()) {
                boolean skip = false;
                for (GraphOrNodeSet<T> constraint : constraints) {
                    if (!constraint.getNodeSet().contains(t)) {
                        skip = true;
                        break;
                    }
                }
                if(!skip) {
                    retSet.add(t);
                }
            }
            return last = Set.of(GraphOrNodeSet.of(retSet));

        }
    }

}

