package hu.bme.mit.theta.xcfa.analysis.stateless.graph.node;

import hu.bme.mit.theta.xcfa.analysis.stateless.State;
import hu.bme.mit.theta.xcfa.analysis.stateless.graph.Edge;

import java.util.HashSet;
import java.util.Set;

public abstract class Node {

    private final Set<Edge> incomingEdges;
    private final Set<Edge> outgoingEdges;

    public Node() {
        outgoingEdges = new HashSet<>();
        incomingEdges = new HashSet<>();
    }

    public Set<Edge> getOutgoingEdges() {
    return outgoingEdges;
    }

    public Set<Edge> getIncomingEdges() {
        return incomingEdges;
    }

    public void addIncomingEdge(Edge edge) {
        incomingEdges.add(edge);
    }

    public void addOutgoingEdge(Edge edge) {
        outgoingEdges.add(edge);
    }

    public void invalidate(State state) {
        for(Edge e : outgoingEdges) {
            e.getTarget().invalidate(state);
        }
        outgoingEdges.clear();
    }

    public abstract Node duplicate();

}
