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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaAction;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaState;

public final class CfaVisualizer {

	private static final String CFA_LABEL = "";
	private static final String CFA_ID = "cfa";
	private static final String LOC_ID_PREFIX = "";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;
	private static final Color CEX_COLOR = Color.RED;

	private static final LineStyle LOC_LINE_STYLE = LineStyle.NORMAL;
	private static final LineStyle EDGE_LINE_STYLE = LineStyle.NORMAL;
	private static final String EDGE_FONT = "courier";

	private CfaVisualizer() {
	}

	public static Graph visualize(final CFA cfa, final Trace<CfaState<?>, CfaAction> cex) {
		final Graph graph = new Graph(CFA_ID, CFA_LABEL);
		final Map<Loc, String> ids = new HashMap<>();

		final Set<Loc> cexLocs = new HashSet<>();
		final Set<Edge> cexEdges = new HashSet<>();
		if (cex != null) {
			cexLocs.addAll(cex.getStates().stream().map(CfaState::getLoc).collect(Collectors.toSet()));
			cexEdges.addAll(cex.getActions().stream().flatMap(a -> a.getEdges().stream()).collect(Collectors.toSet()));
		}

		for (final Loc loc : cfa.getLocs()) {
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
					.lineColor(cexLocs.contains(loc) ? CEX_COLOR : LINE_COLOR).lineStyle(LOC_LINE_STYLE)
					.peripheries(peripheries).build();
			graph.addNode(id, nAttributes);
		}
		for (final Edge edge : cfa.getEdges()) {
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label(edge.getStmt().toString())
					.color(cexEdges.contains(edge) ? CEX_COLOR : LINE_COLOR).lineStyle(EDGE_LINE_STYLE).font(EDGE_FONT)
					.build();
			graph.addEdge(ids.get(edge.getSource()), ids.get(edge.getTarget()), eAttributes);
		}
		return graph;
	}

	public static Graph visualize(final CFA cfa) {
		return visualize(cfa, null);
	}
}
