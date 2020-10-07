package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;
import java.util.Stack;

public class NodeTag extends Filter {
    private final ForEachNode supplier;

    public NodeTag(ForEachNode supplier) {
        this.supplier = supplier;
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        return Set.of(GraphOrNodeSet.of(Set.of(supplier.getCurrentNode())));
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        return null;
    }

    @Override
    protected Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new NodeTag(forEachNodes.peek());
    }
}