package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class ThreadTag<T extends MemoryAccess> extends Filter<T> {
    private final Graph<T> graph;
    private final Map<Process, Set<T>> processMap;
    private final ForEachThread<T> supplier;

    public ThreadTag(Graph<T> graph, ForEachThread<T> supplier) {
        this.graph = graph;
        this.supplier = supplier;
        processMap = new HashMap<>();
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        graph.addEdge(source, target, isFinal);
        processMap.putIfAbsent(supplier.getCurrentProcess(), new HashSet<>());
        processMap.putIfAbsent(source.getProcess(), new HashSet<>());
        processMap.putIfAbsent(target.getProcess(), new HashSet<>());
        processMap.get(source.getProcess()).add(source);
        processMap.get(target.getProcess()).add(target);
        return Set.of(GraphOrNodeSet.of(processMap.get(supplier.getCurrentProcess())));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        graph.removeEdge(source, target);
        if(graph.isDisconnected(source)) processMap.get(source.getProcess()).remove(source);
        if(graph.isDisconnected(target)) processMap.get(source.getProcess()).remove(target);
        processMap.putIfAbsent(supplier.getCurrentProcess(), new HashSet<>());
        return Set.of(GraphOrNodeSet.of(processMap.get(supplier.getCurrentProcess())));
    }
}