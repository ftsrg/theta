package hu.bme.mit.theta.common.visualization.writer;

import hu.bme.mit.theta.common.visualization.Edge;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.Node;
import hu.bme.mit.theta.common.visualization.NodeAttributes;

/**
 * Uses a GraphvizWriter to output a graphviz graph with witness data, but introduces some changes
 * in the given witness graph, as some elements, e.g. non escaped quotation marks in labels will not work with graphviz
 */
public final class WitnessGraphvizWriter extends AbstractGraphWriter {
	Graph modifiedGraph;

	private WitnessGraphvizWriter() {
	}

	private static class LazyHolder {
		static final WitnessGraphvizWriter INSTANCE = new WitnessGraphvizWriter();
	}

	public static WitnessGraphvizWriter getInstance() {
		return WitnessGraphvizWriter.LazyHolder.INSTANCE;
	}

	@Override
	public String writeString(Graph graph) {
		modifiedGraph = new Graph("id", ""); // TODO what should id be?
		graph.getRootNodes().forEach(this::addModifiedNode);

		for (final Node node : graph.getNodes()) {
		 	addModifiedEdge(node);
			// printEdges(node, sb);
		}
		return GraphvizWriter.getInstance().writeString(modifiedGraph);
	}

	private void addModifiedEdge(Node node) {
		for (final Edge edge : node.getOutEdges()) {
			EdgeAttributes edgeAttributes = edge.getAttributes();
			String label = edgeAttributes.getLabel();
			label = label.replace("\"", "\\\"");
			// graphviz throws a syntax error is node names have . in them, so we change them to _dot_
			String source = edge.getSource().getId();
			source = source.replace(".","_dot_");
			String target = edge.getTarget().getId();
			target = target.replace(".","_dot_");
			modifiedGraph.addEdge(source, target, EdgeAttributes.builder().label(label).build());
		}
	}

	private void addModifiedNode(Node n) {
		 NodeAttributes nodeAttributes = n.getAttributes();
		 String label = nodeAttributes.getLabel();
		 label = n.getId() + ": " +label;
		 label = label.replace("\"", "\\\"");
		 // graphviz throws a syntax error is node names have . in them, so we change them to _dot_
		 modifiedGraph.addNode(n.getId().replace(".","_dot_"), NodeAttributes.builder().label(label).build());
	}
}
