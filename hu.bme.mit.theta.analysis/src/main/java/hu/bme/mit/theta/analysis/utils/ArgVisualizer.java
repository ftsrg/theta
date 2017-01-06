package hu.bme.mit.theta.analysis.utils;

import java.awt.Color;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;

public final class ArgVisualizer {

	private static final LineStyle COVER_EDGE_STYLE = LineStyle.DASHED;
	private static final LineStyle SUCC_EDGE_STYLE = LineStyle.NORMAL;
	private static final String ARG_LABEL = "";
	private static final String ARG_ID = "arg";
	private static final String NODE_ID_PREFIX = "node_";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;
	private static final String PHANTOM_INIT_ID = "phantom_init";

	private ArgVisualizer() {
	}

	public static Graph visualize(final ARG<?, ?> arg) {
		final Graph graph = new Graph(ARG_ID, ARG_LABEL);

		final Set<ArgNode<?, ?>> traversed = new HashSet<>();

		for (final ArgNode<?, ?> initNode : arg.getInitNodes().collect(Collectors.toSet())) {
			traverse(graph, initNode, traversed);
			final NodeAttributes nAttributes = NodeAttributes.builder().label("").fillColor(FILL_COLOR)
					.lineColor(FILL_COLOR).lineStyle(SUCC_EDGE_STYLE).peripheries(1).build();
			graph.addNode(PHANTOM_INIT_ID + initNode.getId(), nAttributes);
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label("").color(LINE_COLOR)
					.lineStyle(SUCC_EDGE_STYLE).build();
			graph.addEdge(PHANTOM_INIT_ID + initNode.getId(), NODE_ID_PREFIX + initNode.getId(), eAttributes);
		}

		return graph;
	}

	private static void traverse(final Graph graph, final ArgNode<?, ?> node, final Set<ArgNode<?, ?>> traversed) {
		if (traversed.contains(node)) {
			return;
		} else {
			traversed.add(node);
		}
		final String nodeId = NODE_ID_PREFIX + node.getId();
		final LineStyle lineStyle = SUCC_EDGE_STYLE;
		final int peripheries = node.isTarget() ? 2 : 1;

		final NodeAttributes nAttributes = NodeAttributes.builder().label(node.getState().toString())
				.fillColor(FILL_COLOR).lineColor(LINE_COLOR).lineStyle(lineStyle).peripheries(peripheries).build();

		graph.addNode(nodeId, nAttributes);

		for (final ArgEdge<?, ?> edge : node.getOutEdges().collect(Collectors.toSet())) {
			traverse(graph, edge.getTarget(), traversed);
			final String sourceId = NODE_ID_PREFIX + edge.getSource().getId();
			final String targetId = NODE_ID_PREFIX + edge.getTarget().getId();
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label(edge.getAction().toString())
					.color(LINE_COLOR).lineStyle(SUCC_EDGE_STYLE).build();
			graph.addEdge(sourceId, targetId, eAttributes);
		}

		if (node.getCoveringNode().isPresent()) {
			traverse(graph, node.getCoveringNode().get(), traversed);
			final String sourceId = NODE_ID_PREFIX + node.getId();
			final String targetId = NODE_ID_PREFIX + node.getCoveringNode().get().getId();
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label("").color(LINE_COLOR)
					.lineStyle(COVER_EDGE_STYLE).weight(0).build();
			graph.addEdge(sourceId, targetId, eAttributes);
		}
	}

}
