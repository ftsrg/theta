package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

public class ForEachNode extends Filter {
    private final Filter pattern;
    private Filter op;
    private MemoryAccess currentNode;
    private final Map<MemoryAccess, Filter> ops;
    private final Stack<ForEachNode> forEachNodes;

    public ForEachNode(Filter pattern) {
        this.pattern = pattern;
        this.currentNode = null;
        ops = new HashMap<>();
        forEachNodes = new Stack<>();
        forEachNodes.push(this);
    }

    public ForEachNode(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Filter pattern, Filter op, MemoryAccess currentNode, Map<MemoryAccess, Filter> ops) {
        forEachNodes.push(this);
        this.pattern = pattern.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.op = op.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.currentNode = currentNode;
        this.ops = new HashMap<>();
        ops.forEach((memoryAccess, filter) -> this.ops.put(memoryAccess, filter.duplicate(forEachNodes, forEachVars, forEachThreads)));
        this.forEachNodes = new Stack<>();
        this.forEachNodes.push(this);
        forEachNodes.pop();
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        checkState(op != null, "Set the operand before use!");
        Set<GraphOrNodeSet> patterns = pattern.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (GraphOrNodeSet pattern : patterns) {
            for (MemoryAccess memoryAccess : pattern.getNodeSet()) {
                ops.putIfAbsent(memoryAccess, op.duplicate(this.forEachNodes, new Stack<>(), new Stack<>()));
                currentNode = memoryAccess;
                retSet.addAll(ops.get(memoryAccess).filterMk(source, target, label, isFinal));
            }
        }
        return retSet;
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label){
        checkState(op != null, "Set the operand before use!");
        Set<GraphOrNodeSet> patterns = pattern.filterRm(source, target, label);
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (GraphOrNodeSet pattern : patterns) {
            for (MemoryAccess memoryAccess : pattern.getNodeSet()) {
                ops.putIfAbsent(memoryAccess, op.duplicate(this.forEachNodes, new Stack<>(), new Stack<>()));
                currentNode = memoryAccess;
                retSet.addAll(ops.get(memoryAccess).filterRm(source, target, label));
            }
        }
        return retSet;
    }

    @Override
    public ForEachNode duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new ForEachNode(forEachNodes, forEachVars, forEachThreads, pattern, op, currentNode, ops);
    }

    public void setOp(Filter op) {
        this.op = op;
    }

    public MemoryAccess getCurrentNode() {
        return currentNode;
    }
}
