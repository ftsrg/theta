package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;
import java.util.Stack;

public class NamedEdge extends Filter {
    public final GraphOrNodeSet graph;
    public final String edgeLabel;

    public NamedEdge(String edgeLabel) {
        this.edgeLabel = edgeLabel;
        this.graph = GraphOrNodeSet.of(Graph.empty());
    }

    public NamedEdge(GraphOrNodeSet graph, String edgeLabel) {
        this.graph = graph.duplicate();
        this.edgeLabel = edgeLabel;
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        if(label.equals(this.edgeLabel)) {
            graph.getGraph().addEdge(source, target, isFinal);
            graph.setChanged(true);
        }
        return Set.of(graph);
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        if(label.equals(this.edgeLabel)) {
            graph.getGraph().removeEdge(source, target);
            graph.setChanged(true);
        }
        return Set.of(graph);
    }

    @Override
    protected Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new NamedEdge(graph, edgeLabel);
    }
}
