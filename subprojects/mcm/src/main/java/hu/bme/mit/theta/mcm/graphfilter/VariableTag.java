package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.*;

public class VariableTag extends Filter {
    private final Graph graph;
    private final Map<VarDecl<?>, GraphOrNodeSet> processMap;
    private final ForEachVar supplier;

    public VariableTag(ForEachVar supplier) {
        this.graph = Graph.empty();
        this.supplier = supplier;
        processMap = new HashMap<>();
    }

    public VariableTag(Stack<ForEachVar> forEachVars, Graph graph, Map<VarDecl<?>, GraphOrNodeSet> processMap) {
        this.graph = graph.duplicate();
        this.processMap = new HashMap<>();
        processMap.forEach((variable, memoryAccesses) -> this.processMap.put(variable, memoryAccesses.duplicate()));
        this.supplier = forEachVars.peek();
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        graph.addEdge(source, target, isFinal);
        processMap.putIfAbsent(supplier.getCurrentVariable(), GraphOrNodeSet.of(new HashSet<>()));
        processMap.putIfAbsent(source.getGlobalVariable(), GraphOrNodeSet.of(new HashSet<>()));
        processMap.putIfAbsent(target.getGlobalVariable(), GraphOrNodeSet.of(new HashSet<>()));
        if(processMap.get(source.getGlobalVariable()).getNodeSet().contains(source)) {
            processMap.get(source.getGlobalVariable()).getNodeSet().add(source);
            processMap.get(source.getGlobalVariable()).setChanged(true);
        }
        if(processMap.get(target.getGlobalVariable()).getNodeSet().contains(target)) {
            processMap.get(target.getGlobalVariable()).getNodeSet().add(target);
            processMap.get(target.getGlobalVariable()).setChanged(true);
        }
        return Set.of(processMap.get(supplier.getCurrentVariable()));
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        graph.removeEdge(source, target);
        if(graph.isDisconnected(source)) {
            processMap.get(source.getGlobalVariable()).getNodeSet().remove(source);
            processMap.get(source.getGlobalVariable()).setChanged(true);
        }
        if(graph.isDisconnected(target)) {
            processMap.get(target.getGlobalVariable()).getNodeSet().remove(target);
            processMap.get(target.getGlobalVariable()).setChanged(true);
        }
        processMap.putIfAbsent(supplier.getCurrentVariable(), GraphOrNodeSet.of(new HashSet<>()));
        return Set.of(processMap.get(supplier.getCurrentVariable()));
    }

    @Override
    protected Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new VariableTag(forEachVars, graph, processMap);
    }
}