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
package hu.bme.mit.theta.cfa.analysis.utils;

import java.awt.Color;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Edge;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.visualization.Alignment;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import hu.bme.mit.theta.common.visualization.Shape;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;

public final class CfaVisualizer {

	private static final String CFA_LABEL = "";
	private static final String CFA_ID = "cfa";
	private static final String LOC_ID_PREFIX = "";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;
	private static final LineStyle LOC_LINE_STYLE = LineStyle.NORMAL;
	private static final LineStyle EDGE_LINE_STYLE = LineStyle.NORMAL;
	private static final String EDGE_FONT = "courier";

	private CfaVisualizer() {
	}

	public static Graph visualize(final CFA cfa) {
		final Graph graph = new Graph(CFA_ID, CFA_LABEL);
		final Map<Loc, String> ids = new HashMap<>();
		addVars(graph, cfa);
		for (final Loc loc : cfa.getLocs()) {
			addLocation(graph, cfa, loc, ids);
		}
		for (final Edge edge : cfa.getEdges()) {
			addEdge(graph, edge, ids);
		}
		return graph;
	}

	private static void addVars(final Graph graph, final CFA cfa) {
		final StringBuilder sb = new StringBuilder("Variables");
		for (final VarDecl<?> var : cfa.getVars()) {
			sb.append('\n').append(var.getName()).append(": ").append(var.getType());
		}
		final NodeAttributes attrs = NodeAttributes.builder().label(sb.toString()).shape(Shape.RECTANGLE)
				.fillColor(FILL_COLOR).lineColor(LINE_COLOR).lineStyle(LineStyle.DASHED).alignment(Alignment.LEFT)
				.build();
		graph.addNode(CFA_ID + "_vars", attrs);
	}

	private static void addLocation(final Graph graph, final CFA cfa, final Loc loc, final Map<Loc, String> ids) {
		final String id = LOC_ID_PREFIX + ids.size();
		ids.put(loc, id);
		String label = loc.getName();
		boolean isError = cfa.getErrorLoc().isPresent() && loc == cfa.getErrorLoc().get();
		if (loc == cfa.getInitLoc()) {
			label += " (init)";
		} else if (cfa.getFinalLoc().isPresent() && loc == cfa.getFinalLoc().get()) {
			label += " (end)";
		} else if (isError) {
			label += " (error)";
		}
		final int peripheries = isError ? 2 : 1;
		final NodeAttributes nAttrs = NodeAttributes.builder().label(label).fillColor(FILL_COLOR).lineColor(LINE_COLOR)
				.lineStyle(LOC_LINE_STYLE).peripheries(peripheries).build();
		graph.addNode(id, nAttrs);
	}

	private static void addEdge(final Graph graph, final Edge edge, final Map<Loc, String> ids) {
		final EdgeAttributes eAttrs = EdgeAttributes.builder().label(new CoreDslManager().writeStmt(edge.getStmt()))
				.color(LINE_COLOR).lineStyle(EDGE_LINE_STYLE).font(EDGE_FONT).build();
		graph.addEdge(ids.get(edge.getSource()), ids.get(edge.getTarget()), eAttrs);
	}

	public static void printTraceTable(final Trace<CfaState<ExplState>, CfaAction> trace, final TableWriter writer) {
		final Set<Decl<?>> allVars = new LinkedHashSet<>();
		for (final CfaState<ExplState> state : trace.getStates()) {
			allVars.addAll(state.getState().getDecls());
		}
		final int nCols = 1 + allVars.size();
		writer.startTable();
		writer.cell("LOC");
		allVars.forEach(v -> writer.cell(v.getName()));
		writer.newRow();

		for (int i = 0; i < trace.getStates().size(); i++) {
			final CfaState<ExplState> state = trace.getState(i);
			writer.cell(state.getLoc().getName());
			for (final Decl<?> decl : allVars) {
				final Optional<?> eval = state.getState().eval(decl);
				final String evalStr = eval.isPresent() ? eval.get().toString() : "";
				writer.cell(evalStr);
			}
			writer.newRow();
			if (i < trace.getActions().size()) {
				final StringBuilder sb = new StringBuilder();
				trace.getAction(i).getStmts().forEach(s -> sb.append(s.toString()).append(System.lineSeparator()));
				writer.cell(sb.toString(), nCols);
				writer.newRow();
			}
		}
		writer.endTable();
	}
}
