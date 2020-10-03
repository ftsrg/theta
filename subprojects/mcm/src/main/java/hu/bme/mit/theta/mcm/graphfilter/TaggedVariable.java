package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Variable;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class TaggedVariable<T extends MemoryAccess, L> extends Filter<T, L> {
    private final Graph<T> graph;
    private final Map<Variable, Set<T>> processMap;
    private final ForEachVar<T, L> supplier;

    public TaggedVariable(Graph<T> graph, ForEachVar<T, L> supplier) {
        this.graph = graph;
        this.supplier = supplier;
        processMap = new HashMap<>();
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        graph.addEdge(source, target, isFinal);
        processMap.putIfAbsent(supplier.getCurrentVariable(), new HashSet<>());
        processMap.putIfAbsent(source.getGlobalVariable(), new HashSet<>());
        processMap.putIfAbsent(target.getGlobalVariable(), new HashSet<>());
        processMap.get(source.getGlobalVariable()).add(source);
        processMap.get(target.getGlobalVariable()).add(target);
        return Set.of(GraphOrNodeSet.of(processMap.get(supplier.getCurrentVariable())));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        graph.removeEdge(source, target);
        if(graph.isDisconnected(source)) processMap.get(source.getGlobalVariable()).remove(source);
        if(graph.isDisconnected(target)) processMap.get(source.getGlobalVariable()).remove(target);
        processMap.putIfAbsent(supplier.getCurrentVariable(), new HashSet<>());
        return Set.of(GraphOrNodeSet.of(processMap.get(supplier.getCurrentVariable())));
    }
}