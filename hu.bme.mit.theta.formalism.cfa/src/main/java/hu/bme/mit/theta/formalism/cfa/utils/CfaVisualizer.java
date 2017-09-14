/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *  
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *  
 *      http://www.apache.org/licenses/LICENSE-2.0
 *  
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
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
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

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
		final Map<Loc, String> ids = new HashMap<>();

		for (final Loc loc : cfa.getLocs()) {
			addLocation(graph, cfa, loc, ids);
		}
		for (final Edge edge : cfa.getEdges()) {
			addEdge(graph, cfa, edge, ids);
		}
		return graph;
	}

	private static void addLocation(final Graph graph, final CFA cfa, final Loc loc, final Map<Loc, String> ids) {
		final String id = LOC_ID_PREFIX + ids.size();
		ids.put(loc, id);
		String label = loc.getName();
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

	private static void addEdge(final Graph graph, final CFA cfa, final Edge edge,
			final Map<Loc, String> ids) {
		final StringJoiner edgeLabel = new StringJoiner("\n");
		edge.getStmts().stream().forEach(stmt -> edgeLabel.add(stmt.toString()));
		final EdgeAttributes eAttributes = EdgeAttributes.builder().label(edgeLabel.toString()).color(LINE_COLOR)
				.lineStyle(EDGE_LINE_STYLE).font(EDGE_FONT).build();
		graph.addEdge(ids.get(edge.getSource()), ids.get(edge.getTarget()), eAttributes);
	}
}
