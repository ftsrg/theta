package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

public class EmptySet extends Filter {
    private final Set<GraphOrNodeSet> emptySet;

    public EmptySet() {
        this.emptySet = Set.of(GraphOrNodeSet.of(Graph.empty()));
    }

    private EmptySet(Set<GraphOrNodeSet> emptySet) {
        this.emptySet = new HashSet<>();
        for (GraphOrNodeSet graphOrNodeSet : emptySet) {
            this.emptySet.add(graphOrNodeSet.duplicate());
        }
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        return emptySet;
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        return emptySet;
    }

    @Override
    public Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new EmptySet(emptySet);
    }
}
