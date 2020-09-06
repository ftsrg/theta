package hu.bme.mit.theta.xcfa.analysis.stateless.graph;

import hu.bme.mit.theta.xcfa.analysis.stateless.graph.node.Node;

public class Edge {
    private final Node source;
    private final Node target;
    private final String label;

    public Edge(Node source, Node target, String label) {
        this.source = source;
        this.target = target;
        this.label = label;
    }

    public Node getSource() {
        return source;
    }

    public Node getTarget() {
        return target;
    }

    public String getLabel() {
        return label;
    }
}
