package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;
import java.util.Stack;

public class NodeTag extends Filter {
    private final ForEachNode supplier;
    private GraphOrNodeSet last;

    public NodeTag(ForEachNode supplier) {
        this.supplier = supplier;
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        return last == null ? Set.of(last = GraphOrNodeSet.of(Set.of(supplier.getCurrentNode()))) : Set.of(last);
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        return last == null ? Set.of(last = GraphOrNodeSet.of(Set.of(supplier.getCurrentNode()))) : Set.of(last);
    }

    @Override
    public Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new NodeTag(forEachNodes.peek());
    }
}