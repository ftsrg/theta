package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class NamedEdge<T extends MemoryAccess, L> extends Filter<T, L> {
    public final Graph<T> graph;
    public final L edgeLabel;

    public NamedEdge(L edgeLabel) {
        this.edgeLabel = edgeLabel;
        this.graph = Graph.create(false);
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        if(label.equals(this.edgeLabel)) {
            graph.addEdge(source, target, isFinal);
        }
        return Set.of(GraphOrNodeSet.of(graph));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        if(label.equals(this.edgeLabel)) {
            graph.removeEdge(source, target);
        }
        return Set.of(GraphOrNodeSet.of(graph));
    }
}
