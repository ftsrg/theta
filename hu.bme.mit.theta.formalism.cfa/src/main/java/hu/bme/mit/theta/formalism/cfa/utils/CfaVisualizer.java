package hu.bme.mit.theta.formalism.cfa.utils;

import java.awt.Color;
import java.util.HashMap;
import java.util.Map;
import java.util.StringJoiner;

import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;

public class CfaVisualizer {

	private static final String CFA_LABEL = "";
	private static final String CFA_ID = "cfa";
	private static final String LOC_ID_PREFIX = "";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;
	private static final LineStyle LOC_LINE_STYLE = LineStyle.NORMAL;
	private static final LineStyle EDGE_LINE_STYLE = LineStyle.NORMAL;
	private static final String EDGE_FONT = "courier";

	public static Graph visualize(final CFA cfa) {
		final Graph graph = new Graph(CFA_ID, CFA_LABEL);
		final Map<CfaLoc, String> ids = new HashMap<>();
		traverse(graph, cfa, cfa.getInitLoc(), ids);
		return graph;
	}

	private static void traverse(final Graph graph, final CFA cfa, final CfaLoc loc, final Map<CfaLoc, String> ids) {
		if (!ids.containsKey(loc)) {
			addLocation(graph, cfa, loc, ids);
			for (final CfaEdge outEdge : loc.getOutEdges()) {
				final CfaLoc target = outEdge.getTarget();
				traverse(graph, cfa, target, ids);
				addEdge(graph, cfa, outEdge, ids);
			}
		}
	}

	private static void addLocation(final Graph graph, final CFA cfa, final CfaLoc loc, final Map<CfaLoc, String> ids) {
		final String id = LOC_ID_PREFIX + ids.size();
		ids.put(loc, id);
		String label = id;
		if (loc == cfa.getInitLoc()) {
			label += " (init)";
		} else if (loc == cfa.getFinalLoc()) {
			label += " (end)";
		} else if (loc == cfa.getErrorLoc()) {
			label += " (error)";
		}
		final int peripheries = loc == cfa.getErrorLoc() ? 2 : 1;
		final NodeAttributes nAttributes = NodeAttributes.builder().label(label).fillColor(FILL_COLOR)
				.lineColor(LINE_COLOR).lineStyle(LOC_LINE_STYLE).peripheries(peripheries).build();
		graph.addNode(id, nAttributes);
	}

	private static void addEdge(final Graph graph, final CFA cfa, final CfaEdge outEdge,
			final Map<CfaLoc, String> ids) {
		final StringJoiner edgeLabel = new StringJoiner("\n");
		outEdge.getStmts().stream().forEach(stmt -> edgeLabel.add(stmt.toString()));
		final EdgeAttributes eAttributes = EdgeAttributes.builder().label(edgeLabel.toString()).color(LINE_COLOR)
				.lineStyle(EDGE_LINE_STYLE).font(EDGE_FONT).build();
		graph.addEdge(ids.get(outEdge.getSource()), ids.get(outEdge.getTarget()), eAttributes);
	}
}
