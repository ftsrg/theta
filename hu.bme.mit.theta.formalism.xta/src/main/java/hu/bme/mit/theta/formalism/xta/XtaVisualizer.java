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
package hu.bme.mit.theta.formalism.xta;

import java.awt.Color;
import java.util.HashMap;
import java.util.Map;
import java.util.StringJoiner;

import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

public final class XtaVisualizer {

	private static final String XTA_LABEL = "";
	private static final String LOC_ID_PREFIX = "loc_";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;
	private static final LineStyle LOC_LINE_STYLE = LineStyle.NORMAL;
	private static final LineStyle EDGE_LINE_STYLE = LineStyle.NORMAL;
	private static final int LOC_PERIPHERIES = 1;
	private static final String PHANTOM_INIT_ID = "phantom_init";

	private XtaVisualizer() {
	}

	public static Graph visualize(final XtaSystem system) {
		final Graph graph = new Graph("System", XTA_LABEL);
		final Map<Object, String> ids = new HashMap<>();
		for (final XtaProcess process : system.getProcesses()) {
			traverseProcess(process, graph, ids);
		}
		return graph;
	}

	public static Graph visualize(final XtaProcess process) {
		final Graph graph = new Graph(process.getName(), XTA_LABEL);
		final Map<Object, String> ids = new HashMap<>();
		traverseProcess(process, graph, ids);
		return graph;
	}

	private static void traverseProcess(final XtaProcess process, final Graph graph, final Map<Object, String> ids) {
		traverse(graph, process.getInitLoc(), ids);
		final String phantomId = PHANTOM_INIT_ID + ids.get(process.getInitLoc());
		final NodeAttributes nAttributes = NodeAttributes.builder().label("").fillColor(FILL_COLOR)
				.lineColor(FILL_COLOR).lineStyle(LOC_LINE_STYLE).peripheries(LOC_PERIPHERIES).build();
		graph.addNode(phantomId, nAttributes);
		final EdgeAttributes eAttributes = EdgeAttributes.builder().label("").color(LINE_COLOR)
				.lineStyle(EDGE_LINE_STYLE).build();
		graph.addEdge(phantomId, ids.get(process.getInitLoc()), eAttributes);
	}

	private static void traverse(final Graph graph, final Loc loc, final Map<Object, String> ids) {
		if (!ids.containsKey(loc)) {
			addLocation(graph, loc, ids);
			for (final Edge outEdge : loc.getOutEdges()) {
				final Loc target = outEdge.getTarget();
				traverse(graph, target, ids);
				addEdge(graph, ids, outEdge);
			}
		}
	}

	private static void addLocation(final Graph graph, final Loc loc, final Map<Object, String> ids) {
		final String id = LOC_ID_PREFIX + ids.size();
		ids.put(loc, id);
		final StringJoiner locLabel = new StringJoiner("\n", loc.getName() + "\n", "");
		loc.getInvars().forEach(expr -> locLabel.add(expr.toString()));
		final NodeAttributes nAttributes = NodeAttributes.builder().label(locLabel.toString()).fillColor(FILL_COLOR)
				.lineColor(LINE_COLOR).lineStyle(LOC_LINE_STYLE).peripheries(LOC_PERIPHERIES).build();
		graph.addNode(id, nAttributes);
	}

	private static void addEdge(final Graph graph, final Map<Object, String> ids, final Edge outEdge) {
		final StringJoiner edgeLabel = new StringJoiner("\n");
		outEdge.getLabel().ifPresent(sync -> edgeLabel.add(sync.toString()));
		outEdge.getGuards().stream().forEach(expr -> edgeLabel.add("\\[" + expr.toString() + "\\]"));
		outEdge.getUpdates().stream().forEach(stmt -> edgeLabel.add(stmt.toString()));
		final EdgeAttributes attributes = EdgeAttributes.builder().label(edgeLabel.toString()).color(LINE_COLOR)
				.lineStyle(EDGE_LINE_STYLE).build();
		graph.addEdge(ids.get(outEdge.getSource()), ids.get(outEdge.getTarget()), attributes);
	}

}
