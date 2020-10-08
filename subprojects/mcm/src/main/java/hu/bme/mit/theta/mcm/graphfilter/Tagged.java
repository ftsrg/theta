package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import static com.google.common.base.Preconditions.checkState;

public class Tagged extends Filter {
    private final Set<Filter> tags;
    private final Filter named;
    private Set<GraphOrNodeSet> last;

    public Tagged(Set<Filter> tags, Filter named) {
        this.tags = tags;
        this.named = named;
        this.last = new HashSet<>();
    }

    public Tagged(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Set<Filter> tags, Filter named, Set<GraphOrNodeSet> last) {
        this.tags = new HashSet<>();
        tags.forEach(filter -> this.tags.add(filter.duplicate(forEachNodes, forEachVars, forEachThreads)));
        this.named = named.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.last = new HashSet<>();
        last.forEach(graphOrNodeSet -> this.last.add(graphOrNodeSet.duplicate()));
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        Set<GraphOrNodeSet> baseSet = named.filterMk(source, target, label, isFinal);
        checkState(baseSet.size() == 1, "Tagged expression cannot handle more than one nodeset from its named expression!");
        GraphOrNodeSet base = baseSet.iterator().next();
        Set<GraphOrNodeSet> constraints = new HashSet<>();
        for (Filter tag : tags) {
            constraints.addAll(tag.filterMk(source, target, label, isFinal));
        }
        return getTagged(base, constraints);
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> baseSet = named.filterRm(source, target, label);
        checkState(baseSet.size() == 1, "Tagged expression cannot handle more than one nodeset from its named expression!");
        GraphOrNodeSet base = baseSet.iterator().next();
        Set<GraphOrNodeSet> constraints = new HashSet<>();
        for (Filter tag : tags) {
            constraints.addAll(tag.filterRm(source, target, label));
        }
        return getTagged(base, constraints);
    }

    @Override
    public Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new Tagged(forEachNodes, forEachVars, forEachThreads, tags, named, last);
    }

    private Set<GraphOrNodeSet> getTagged(GraphOrNodeSet base, Set<GraphOrNodeSet> constraints) {
        boolean changed = false;
        checkState(!base.isGraph(), "Cannot filter graphs!");
        if(base.isChanged()) {
            changed = true;
            base.setChanged(false);
        }
        for (GraphOrNodeSet constraint : constraints) {
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
            Set<MemoryAccess> retSet = new HashSet<>();
            for (MemoryAccess t : base.getNodeSet()) {
                boolean skip = false;
                for (GraphOrNodeSet constraint : constraints) {
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

