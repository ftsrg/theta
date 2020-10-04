package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class NamedEdge<T extends MemoryAccess> extends Filter<T> {
    public final GraphOrNodeSet<T> graph;
    public final String edgeLabel;

    public NamedEdge(String edgeLabel) {
        this.edgeLabel = edgeLabel;
        this.graph = GraphOrNodeSet.of(Graph.create(false));
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        if(label.equals(this.edgeLabel)) {
            graph.getGraph().addEdge(source, target, isFinal);
            graph.setChanged(true);
        }
        return Set.of(graph);
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        if(label.equals(this.edgeLabel)) {
            graph.getGraph().removeEdge(source, target);
            graph.setChanged(true);
        }
        return Set.of(graph);
    }
}
