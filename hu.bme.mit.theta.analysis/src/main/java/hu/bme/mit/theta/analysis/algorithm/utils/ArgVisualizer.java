package hu.bme.mit.theta.analysis.algorithm.utils;

import java.awt.Color;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;

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

		graph.addNode(nodeId, node.getState().toString(), FILL_COLOR, LINE_COLOR, lineStyle, peripheries);

		for (final ArgEdge<?, ?> edge : node.getOutEdges()) {
			traverse(graph, edge.getTarget());
			final String sourceId = NODE_ID_PREFIX + edge.getSource().getId();
			final String targetId = NODE_ID_PREFIX + edge.getTarget().getId();
			graph.addEdge(sourceId, targetId, "", LINE_COLOR, LineStyle.NORMAL);
		}

		if (node.getCoveringNode().isPresent()) {
			final String sourceId = NODE_ID_PREFIX + node.getId();
			final String targetId = NODE_ID_PREFIX + node.getCoveringNode().get().getId();
			graph.addEdge(sourceId, targetId, "", LINE_COLOR, LineStyle.DASHED);
		}
	}

}
