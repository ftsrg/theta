package hu.bme.mit.theta.common.visualization;

import java.awt.Color;
import java.util.HashMap;
import java.util.Map;

public final class GraphVizPrinter implements GraphPrinter {

	@Override
	public String print(final Graph graph) {
		final StringBuilder sb = new StringBuilder();
		sb.append("digraph ").append(graph.getId()).append(" {").append(System.lineSeparator());
		sb.append("\tlabel=\"").append(graph.getLabel()).append("\";").append(System.lineSeparator());

		for (final Node node : graph.getNodes()) {
			printNode(node, sb);
		}

		for (final Node node : graph.getNodes()) {
			printEdges(node, sb);
		}
		sb.append("}");
		return sb.toString();
	}

	private void printNode(final Node node, final StringBuilder sb) {
		if (node instanceof CompositeNode) {
			printCompositeNode((CompositeNode) node, sb);
		}
		String style = node.getLineStyle();
		if (style.equals("")) {
			style += "filled";
		} else {
			style += ",filled";
		}

		sb.append("\t\t").append(node.getId());
		sb.append(" [label=\"").append(node.getLabel().replace("\n", "\\n")).append("\"");
		if (node.getPeripheries() > 1) {
			sb.append(",peripheries=").append(node.getPeripheries());
		}
		sb.append(",style=\"").append(style).append("\"");
		sb.append(",fillcolor=").append(mapColorToString(node.getFillColor()));
		sb.append(",color=").append(mapColorToString(node.getEdgeColor()));
		sb.append("];").append(System.lineSeparator());
	}

	private void printCompositeNode(final CompositeNode node, final StringBuilder sb) {
		sb.append("\tsubgraph ").append(node.getId()).append(" {").append(System.lineSeparator());
		sb.append("\t\tcolor=").append(node.getEdgeColor()).append(";").append(System.lineSeparator());
		sb.append("\t\tstyle=filled;").append(System.lineSeparator());
		sb.append("\t\tfillcolor=").append(node.getFillColor()).append(";").append(System.lineSeparator());
		sb.append("\t\tlabel=\"").append(node.getLabel().replace("\n", "\\n")).append("\";")
				.append(System.lineSeparator());
		// TODO: peripheries?
		for (final Node child : node.getChildren()) {
			if (node instanceof CompositeNode) {
				printCompositeNode((CompositeNode) child, sb);
			} else {
				printNode(child, sb);
			}
		}
		sb.append("\t}").append(System.lineSeparator());
	}

	private void printEdges(final Node node, final StringBuilder sb) {
		// To the best of my knowledge, GraphViz does not support edges between
		// clusters, thus such edges are ignored
		if (node instanceof CompositeNode) {
			for (final Node child : ((CompositeNode) node).getChildren()) {
				printEdges(child, sb);
			}
		} else {
			for (final Edge edge : node.getOutEdges()) {
				sb.append("\t").append(edge.getSource().getId()).append(" -> ").append(edge.getTarget().getId());
				sb.append(" [label=\"").append(edge.getLabel().replace("\n", "\\n")).append("\"");
				sb.append(",color=").append(mapColorToString(edge.getEdgeColor())).append("];");
				// TODO: edge style
				sb.append(System.lineSeparator());
			}
		}
	}

	@SuppressWarnings("serial")
	private static final Map<Color, String> colors = new HashMap<Color, String>() {
		{
			put(Color.BLACK, "black");
			put(Color.WHITE, "white");
			put(Color.RED, "red");
		}
	};

	private String mapColorToString(final Color color) {
		if (colors.containsKey(color)) {
			return colors.get(color);
		} else {
			// TODO
			return "black";
		}
	}
}
