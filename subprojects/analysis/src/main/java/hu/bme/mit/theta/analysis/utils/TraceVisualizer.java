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
package hu.bme.mit.theta.analysis.utils;

import java.awt.Color;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;

public final class TraceVisualizer<S extends State, A extends Action> {

	private static final LineStyle LINE_STYLE = LineStyle.NORMAL;
	private static final String STATE_ID_PREFIX = "s_";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;
	private static final String TRACE_LABEL = "";
	private static final String TRACE_ID = "trace";

	private final Function<S, String> stateToString;
	private final Function<A, String> actionToString;

	private static class LazyHolder {
		static final TraceVisualizer<State, Action> DEFAULT = new TraceVisualizer<>(s -> s.toString(),
				a -> a.toString());
	}

	public TraceVisualizer(final Function<S, String> stateToString, final Function<A, String> actionToString) {
		this.stateToString = stateToString;
		this.actionToString = actionToString;
	}

	public static TraceVisualizer<State, Action> getDefault() {
		return LazyHolder.DEFAULT;
	}

	public Graph visualize(final Trace<? extends S, ? extends A> trace) {
		final Graph graph = new Graph(TRACE_ID, TRACE_LABEL);

		for (int i = 0; i < trace.getStates().size(); ++i) {
			final NodeAttributes nAttributes = NodeAttributes.builder().label(stateToString.apply(trace.getState(i)))
					.fillColor(FILL_COLOR).lineColor(LINE_COLOR).lineStyle(LINE_STYLE).build();
			graph.addNode(STATE_ID_PREFIX + i, nAttributes);
		}

		for (int i = 0; i < trace.getActions().size(); ++i) {
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label(actionToString.apply(trace.getAction(i)))
					.color(LINE_COLOR).lineStyle(LINE_STYLE).build();
			graph.addEdge(STATE_ID_PREFIX + i, STATE_ID_PREFIX + (i + 1), eAttributes);
		}

		return graph;
	}

	public Graph visualizeMerged(final Collection<? extends Trace<? extends S, ? extends A>> traces) {
		final Graph graph = new Graph(TRACE_ID, TRACE_LABEL);

		final Map<S, String> stateIds = new HashMap<>();

		for (final Trace<? extends S, ? extends A> trace : traces) {
			for (final S state : trace.getStates()) {
				if (!stateIds.containsKey(state)) {
					stateIds.put(state, STATE_ID_PREFIX + stateIds.size());
					final NodeAttributes nAttributes = NodeAttributes.builder().label(stateToString.apply(state))
							.fillColor(FILL_COLOR).lineColor(LINE_COLOR).lineStyle(LINE_STYLE).build();
					graph.addNode(stateIds.get(state), nAttributes);
				}
			}
		}

		int traceNo = 0;

		for (final Trace<? extends S, ? extends A> trace : traces) {
			for (int i = 0; i < trace.getActions().size(); ++i) {
				final A action = trace.getAction(i);
				final S source = trace.getState(i);
				final S target = trace.getState(i + 1);
				final Color color = Color.getHSBColor(traceNo / (float) traces.size(), 1, 1);
				final EdgeAttributes eAttributes = EdgeAttributes.builder().label(actionToString.apply(action))
						.color(color).lineStyle(LINE_STYLE).build();
				graph.addEdge(stateIds.get(source), stateIds.get(target), eAttributes);
			}
			++traceNo;
		}

		return graph;
	}
}
