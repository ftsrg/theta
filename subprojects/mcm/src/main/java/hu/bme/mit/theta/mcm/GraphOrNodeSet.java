package hu.bme.mit.theta.mcm;

import java.util.Set;

public class GraphOrNodeSet<T> {
    private boolean changed;
    private final boolean isGraph;
    private final Graph<T> graph;
    private final Set<T> nodeSet;

    private GraphOrNodeSet(Graph<T> graph) {
        isGraph = true;
        this.graph = graph;
        this.nodeSet = null;
        this.changed = true;
    }

    private GraphOrNodeSet(Set<T> nodeSet) {
        isGraph = false;
        this.graph = null;
        this.nodeSet = nodeSet;
        this.changed = true;
    }

    public static <T> GraphOrNodeSet<T> of(Graph<T> graph) {
        return new GraphOrNodeSet<T>(graph);
    }

    public static <T> GraphOrNodeSet<T> of(Set<T> nodeSet) {
        return new GraphOrNodeSet<T>(nodeSet);
    }

    public boolean isGraph() {
        return isGraph;
    }

    public Set<T> getNodeSet() {
        return nodeSet;
    }

    public Graph<T> getGraph() {
        return graph;
    }

    public boolean isChanged() {
        return changed;
    }

    public void setChanged(boolean changed) {
        this.changed = changed;
    }
}
