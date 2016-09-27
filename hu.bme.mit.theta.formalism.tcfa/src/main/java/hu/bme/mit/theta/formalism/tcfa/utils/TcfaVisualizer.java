package hu.bme.mit.theta.formalism.tcfa.utils;

import java.awt.Color;
import java.util.HashMap;
import java.util.Map;
import java.util.StringJoiner;

import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public class TcfaVisualizer {

	private static final String LOC_ID_PREFIX = "loc_";
	private static final Color LOC_FILL_COLOR = Color.WHITE;
	private static final Color LOC_EDGE_COLOR = Color.BLACK;
	private static final Color EDGE_COLOR = Color.BLACK;
	private static final String LOC_LINE_STYLE = "";
	private static final String EDGE_LINE_STYLE = "";

	public static Graph visualize(final TCFA tcfa) {
		final Graph graph = new Graph("tcfa", "");

		final Map<TcfaLoc, String> ids = new HashMap<>();

		graph.addNode("phantom_init", "", Color.WHITE, Color.WHITE, "", 1);
		for (final TcfaLoc loc : tcfa.getLocs()) {
			final String id = LOC_ID_PREFIX + ids.size();
			ids.put(loc, id);
			final StringJoiner label = new StringJoiner("\n", loc.getName() + "\n", "");
			loc.getInvars().forEach(expr -> label.add(expr.toString()));
			graph.addNode(id, label.toString(), LOC_FILL_COLOR, LOC_EDGE_COLOR, LOC_LINE_STYLE, 1);
		}

		graph.addEdge("phantom_init", ids.get(tcfa.getInitLoc()), "", EDGE_COLOR, "");
		for (final TcfaEdge edge : tcfa.getEdges()) {
			final StringJoiner label = new StringJoiner("\n");
			edge.getStmts().stream().forEach(stmt -> label.add(stmt.toString()));
			graph.addEdge(ids.get(edge.getSource()), ids.get(edge.getTarget()), label.toString(), EDGE_COLOR,
					EDGE_LINE_STYLE);
		}

		return graph;
	}
}
