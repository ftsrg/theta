package hu.bme.mit.inf.theta.analysis.algorithm;

import static java.lang.System.lineSeparator;

import hu.bme.mit.inf.theta.analysis.algorithm.impl.ARG;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.ArgEdge;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.ArgNode;

public class ArgPrinter {

	private ArgPrinter() {
	}

	public static String toGraphvizString(final ARG<?, ?, ?> arg) {
		final StringBuilder sb = new StringBuilder();

		sb.append("digraph arg {");
		sb.append(lineSeparator());

		for (final ArgNode<?, ?> initNode : arg.getInitNodes()) {
			appendNode(sb, initNode);
		}

		sb.append("}");
		return sb.toString();
	}

	public static String toGraphvizString(final ArgNode<?, ?> node) {
		final StringBuilder sb = new StringBuilder();

		sb.append("digraph arg {\\n");
		sb.append(lineSeparator());

		appendNode(sb, node);

		sb.append("}");
		return sb.toString();
	}

	private static void appendNode(final StringBuilder sb, final ArgNode<?, ?> node) {
		sb.append(Integer.toString(node.getId()));
		sb.append(" [label=\"");
		sb.append(node.getState());
		sb.append("\"]");
		if (node.isTarget()) {
			sb.append("[peripheries=2]");
		} else if (!node.isExpanded()) {
			sb.append("[style=\"dashed\"]");
		}
		sb.append(lineSeparator());

		for (final ArgEdge<?, ?> edge : node.getOutEdges()) {
			appendNode(sb, edge.getTarget());
			appendEdge(sb, edge);
		}

		if (node.getCoveringNode().isPresent()) {
			appendCover(sb, node, node.getCoveringNode().get());
		}
	}

	private static void appendEdge(final StringBuilder sb, final ArgEdge<?, ?> edge) {
		sb.append(Integer.toString(edge.getSource().getId()));
		sb.append(" -> ");
		sb.append(Integer.toString(edge.getTarget().getId()));
		sb.append(lineSeparator());
	}

	private static void appendCover(final StringBuilder sb, final ArgNode<?, ?> node,
			final ArgNode<?, ?> coveringNode) {
		sb.append(node.getId());
		sb.append(" -> ");
		sb.append(coveringNode.getId());
		sb.append(" [style=\"dashed\"]");
		sb.append(lineSeparator());
	}

	////

}
