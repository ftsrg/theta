package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

public class NamedNode<T extends MemoryAccess, L> extends Filter<T, L> {
    private final Class<?> clazz;
    private final Graph<T> graph;
    private final Set<T> set;

    public NamedNode(Class<?> clazz) {
        this.clazz = clazz;
        set = new HashSet<>();
        graph = Graph.create(false);
    }


    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        graph.addEdge(source, target, isFinal);
        if(clazz.isInstance(source)) {
            set.add(source);
        }
        if(clazz.isInstance(target)) {
            set.add(target);
        }
        return Set.of(GraphOrNodeSet.of(set));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        graph.removeEdge(source, target);
        if(graph.isDisconnected(source)) set.remove(source);
        if(graph.isDisconnected(target)) set.remove(target);
        return Set.of(GraphOrNodeSet.of(set));
    }
}
