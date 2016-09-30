package hu.bme.mit.theta.analysis.utils;

import java.awt.Color;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;

public class ArgVisualizer {

	private static final String ARG_LABEL = "";
	private static final String ARG_ID = "arg";
	private static final String NODE_ID_PREFIX = "node_";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;

	public static Graph visualize(final ARG<?, ?, ?> arg) {
		final Graph graph = new Graph(ARG_ID, ARG_LABEL);

		for (final ArgNode<?, ?> initNode : arg.getInitNodes()) {
			traverse(graph, initNode);
		}

		return graph;
	}

	private static void traverse(final Graph graph, final ArgNode<?, ?> node) {
		final String nodeId = NODE_ID_PREFIX + node.getId();
		final LineStyle lineStyle = node.isExpanded() || node.isTarget() ? LineStyle.NORMAL : LineStyle.DASHED;
		final int peripheries = node.isTarget() ? 2 : 1;

		final NodeAttributes nAttributes = NodeAttributes.builder().label(node.getState().toString())
				.fillColor(FILL_COLOR).lineColor(LINE_COLOR).lineStyle(lineStyle).peripheries(peripheries).build();

		graph.addNode(nodeId, nAttributes);

		for (final ArgEdge<?, ?> edge : node.getOutEdges()) {
			traverse(graph, edge.getTarget());
			final String sourceId = NODE_ID_PREFIX + edge.getSource().getId();
			final String targetId = NODE_ID_PREFIX + edge.getTarget().getId();
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label("").color(LINE_COLOR)
					.lineStyle(LineStyle.NORMAL).build();
			graph.addEdge(sourceId, targetId, eAttributes);
		}

		if (node.getCoveringNode().isPresent()) {
			final String sourceId = NODE_ID_PREFIX + node.getId();
			final String targetId = NODE_ID_PREFIX + node.getCoveringNode().get().getId();
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label("").color(LINE_COLOR)
					.lineStyle(LineStyle.DASHED).build();
			graph.addEdge(sourceId, targetId, eAttributes);
		}
	}

}
