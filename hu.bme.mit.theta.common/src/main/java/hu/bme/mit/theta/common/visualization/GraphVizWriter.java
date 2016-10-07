package hu.bme.mit.theta.common.visualization;

import java.awt.Color;
import java.util.HashMap;
import java.util.Map;

/**
 * Class for writing graphs in GraphViz format.
 *
 * Known limitations (due to GraphViz):
 *
 * - Fill color of composite nodes is ignored.
 *
 * - Shape of composite nodes is ignored.
 *
 * - Peripheries of composite nodes are ignored.
 */
public final class GraphVizWriter extends AbstractGraphWriter {

	@Override
	public String writeString(final Graph graph) {
		final StringBuilder sb = new StringBuilder();
		sb.append("digraph ").append(graph.getId()).append(" {").append(System.lineSeparator());
		sb.append("\tlabel=\"").append(graph.getLabel()).append("\";").append(System.lineSeparator());

		for (final Node node : graph.getNodes()) {
			if (node.getParent() == null) {
				printNode(node, sb);
			}
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
		} else {
			printSimpleNode(node, sb);
		}

	}

	private void printSimpleNode(final Node node, final StringBuilder sb) {
		final NodeAttributes attributes = node.getAttributes();

		String style = mapLineStyleToString(attributes.getLineStyle());
		if (!style.equals("")) {
			style += ",";
		}
		style += "filled";

		sb.append("\t\t").append(node.getId());
		sb.append(" [label=\"").append(attributes.getLabel().replace("\n", "\\n")).append("\"");
		if (attributes.getPeripheries() > 1) {
			sb.append(",peripheries=").append(attributes.getPeripheries());
		}
		sb.append(",style=\"").append(style).append("\"");
		sb.append(",fillcolor=").append(mapColorToString(attributes.getFillColor()));
		sb.append(",color=").append(mapColorToString(attributes.getLineColor()));
		sb.append(",shape=").append(mapShapeToString(attributes.getShape()));
		sb.append("];").append(System.lineSeparator());
	}

	private void printCompositeNode(final CompositeNode node, final StringBuilder sb) {
		final NodeAttributes attributes = node.getAttributes();
		final String style = mapLineStyleToString(attributes.getLineStyle());

		sb.append("\tsubgraph cluster_").append(node.getId()).append(" {").append(System.lineSeparator());
		sb.append("\t\tcolor=").append(mapColorToString(attributes.getLineColor())).append(";")
				.append(System.lineSeparator());
		if (!style.equals("")) {
			sb.append("\t\tstyle=").append(style).append(";").append(System.lineSeparator());
		}
		sb.append("\t\tlabel=\"").append(attributes.getLabel().replace("\n", "\\n")).append("\";")
				.append(System.lineSeparator());
		for (final Node child : node.getChildren()) {
			printNode(child, sb);
		}
		sb.append("\t}").append(System.lineSeparator());
	}

	private void printEdges(final Node node, final StringBuilder sb) {
		if (node instanceof CompositeNode) {
			if (node.getOutEdges().size() != 0) {
				throw new UnsupportedOperationException("GraphViz does not support edges between clusters.");
			}
		} else {
			for (final Edge edge : node.getOutEdges()) {
				final EdgeAttributes attributes = edge.getAttributes();
				sb.append("\t").append(edge.getSource().getId()).append(" -> ").append(edge.getTarget().getId());
				sb.append(" [label=\"").append(attributes.getLabel().replace("\n", "\\n")).append("\"");
				sb.append(",color=").append(mapColorToString(attributes.getColor()));
				final String style = mapLineStyleToString(attributes.getLineStyle());
				if (!style.equals("")) {
					sb.append(",style=").append(style);
				}
				if (!attributes.getFont().equals("")) {
					sb.append(",fontname=\"").append(attributes.getFont()).append("\"");
				}
				sb.append("];").append(System.lineSeparator());
			}
		}
	}

	@SuppressWarnings("serial")
	private static final Map<Color, String> COLORS = new HashMap<Color, String>() {
		{
			put(Color.BLACK, "black");
			put(Color.WHITE, "white");
			put(Color.RED, "red");
			put(Color.BLUE, "blue");
			put(Color.GREEN, "green");
			put(Color.YELLOW, "yellow");
		}
	};

	private String mapColorToString(final Color color) {
		if (COLORS.containsKey(color)) {
			return COLORS.get(color);
		} else {
			throw new UnsupportedOperationException("Unknown color: " + color + ".");
		}
	}

	private String mapLineStyleToString(final LineStyle lineStyle) {
		switch (lineStyle) {
		case DASHED:
			return "dashed";
		case DOTTED:
			return "dotted";
		case NORMAL:
			return "solid";
		default:
			throw new UnsupportedOperationException("Unknown line style: " + lineStyle + ".");
		}
	}

	private String mapShapeToString(final Shape shape) {
		switch (shape) {
		case CIRCLE:
			return "circle";
		case ELLIPSE:
			return "ellipse";
		case RECTANGLE:
			return "rectangle";
		default:
			throw new UnsupportedOperationException("Unknown shape: " + shape + ".");
		}
	}
}
