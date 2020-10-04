package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

public class NamedNode<T extends MemoryAccess> extends Filter<T> {
    private final Class<?> clazz;
    private final Graph<T> graph;
    private final GraphOrNodeSet<T> set;

    public NamedNode(Class<?> clazz) {
        this.clazz = clazz;
        set = GraphOrNodeSet.of(new HashSet<>());
        graph = Graph.create(false);
    }


    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        graph.addEdge(source, target, isFinal);
        if((clazz == null || clazz.isInstance(source)) && !set.getNodeSet().contains(source)) {
            set.getNodeSet().add(source);
            set.setChanged(true);
        }
        if((clazz == null || clazz.isInstance(target)) && !set.getNodeSet().contains(target)) {
            set.getNodeSet().add(target);
            set.setChanged(true);
        }
        return Set.of(set);
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        graph.removeEdge(source, target);
        if(graph.isDisconnected(source)) {
            set.getNodeSet().remove(source);
            set.setChanged(true);
        }
        if(graph.isDisconnected(target)) {
            set.getNodeSet().remove(target);
            set.setChanged(true);
        }
        return Set.of(set);
    }
}
