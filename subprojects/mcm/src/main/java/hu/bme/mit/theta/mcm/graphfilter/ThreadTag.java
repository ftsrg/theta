package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;

import java.util.*;

public class ThreadTag extends Filter {
    private final Graph graph;
    private final Map<Process, GraphOrNodeSet> processMap;
    private final ForEachThread supplier;

    public ThreadTag(ForEachThread supplier) {
        this.graph = Graph.empty();
        this.supplier = supplier;
        processMap = new HashMap<>();
    }

    public ThreadTag(Stack<ForEachThread> forEachThreads, Graph graph, Map<Process, GraphOrNodeSet> processMap) {
        this.graph = graph.duplicate();
        this.processMap = new HashMap<>();
        processMap.forEach((process, memoryAccesses) -> this.processMap.put(process, memoryAccesses.duplicate()));
        this.supplier = forEachThreads.peek();
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        graph.addEdge(source, target, isFinal);
        processMap.putIfAbsent(supplier.getCurrentProcess(), GraphOrNodeSet.of(new HashSet<>()));
        processMap.putIfAbsent(source.getProcess(), GraphOrNodeSet.of(new HashSet<>()));
        processMap.putIfAbsent(target.getProcess(), GraphOrNodeSet.of(new HashSet<>()));
        if(processMap.get(source.getProcess()).getNodeSet().contains(source)) {
            processMap.get(source.getProcess()).getNodeSet().add(source);
            processMap.get(source.getProcess()).setChanged(true);
        }
        if(processMap.get(target.getProcess()).getNodeSet().contains(target)) {
            processMap.get(target.getProcess()).getNodeSet().add(target);
            processMap.get(target.getProcess()).setChanged(true);
        }
        return Set.of(processMap.get(supplier.getCurrentProcess()));
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        graph.removeEdge(source, target);
        if(graph.isDisconnected(source)) {
            processMap.get(source.getProcess()).getNodeSet().remove(source);
            processMap.get(source.getProcess()).setChanged(true);
        }
        if(graph.isDisconnected(target)) {
            processMap.get(target.getProcess()).getNodeSet().remove(target);
            processMap.get(target.getProcess()).setChanged(true);
        }
        processMap.putIfAbsent(supplier.getCurrentProcess(), GraphOrNodeSet.of(new HashSet<>()));
        return Set.of(processMap.get(supplier.getCurrentProcess()));
    }

    @Override
    protected Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new ThreadTag(forEachThreads, graph, processMap);
    }
}