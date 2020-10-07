package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

public class SetMinus extends Filter {
    private final Filter lhs;
    private final Filter rhs;
    private Set<GraphOrNodeSet> last;

    public SetMinus(Filter lhs, Filter rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.last = new HashSet<>();
    }

    public SetMinus(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Filter lhs, Filter rhs, Set<GraphOrNodeSet> last) {
        this.lhs = lhs.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.rhs = rhs.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.last = new HashSet<>();
        last.forEach(graphOrNodeSet -> this.last.add(graphOrNodeSet.duplicate()));
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        Set<GraphOrNodeSet> lhsSet = this.lhs.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet> rhsSet = this.rhs.filterMk(source, target, label, isFinal);
        return getSets(lhsSet, rhsSet);
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> lhsSet = this.lhs.filterRm(source, target, label);
        Set<GraphOrNodeSet> rhsSet = this.rhs.filterRm(source, target, label);
        return getSets(lhsSet, rhsSet);
    }

    @Override
    protected Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new SetMinus(forEachNodes, forEachVars, forEachThreads, lhs, rhs, last);
    }

    private Set<GraphOrNodeSet> getSets(Set<GraphOrNodeSet> lhsSet, Set<GraphOrNodeSet> rhsSet) {
        boolean changed = false;
        for (GraphOrNodeSet lhs : lhsSet) {
            if(lhs.isChanged()) {
                changed = true;
                lhs.setChanged(false);
            }
        }
        for (GraphOrNodeSet rhs : rhsSet) {
            if(rhs.isChanged()) {
                changed = true;
                rhs.setChanged(false);
            }
        }
        if(!changed) {
            return last;
        }
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (GraphOrNodeSet lhs : lhsSet) {
            for (GraphOrNodeSet rhs : rhsSet) {
                retSet.add(getMinus(lhs, rhs));
            }
        }
        return last = retSet;
    }

    private GraphOrNodeSet getMinus(GraphOrNodeSet lhs, GraphOrNodeSet rhs) {
        if (lhs.isGraph() && rhs.isGraph()) {
            return GraphOrNodeSet.of(lhs.getGraph().minus(rhs.getGraph()));
        } else if (!lhs.isGraph() && !rhs.isGraph()) {
            Set<MemoryAccess> lhsSet = new HashSet<>(lhs.getNodeSet());
            lhsSet.removeAll(rhs.getNodeSet());
            return GraphOrNodeSet.of(lhsSet);
        } else throw new UnsupportedOperationException("Cannot take the difference of nodes and a graph!");
    }
}

