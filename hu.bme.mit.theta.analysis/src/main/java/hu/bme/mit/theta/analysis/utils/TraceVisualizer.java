package hu.bme.mit.theta.analysis.utils;

import java.awt.Color;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;

public final class TraceVisualizer {

	private static final LineStyle LINE_STYLE = LineStyle.NORMAL;
	private static final String STATE_ID_PREFIX = "s_";
	private static final Color FILL_COLOR = Color.WHITE;
	private static final Color LINE_COLOR = Color.BLACK;
	private static final String TRACE_LABEL = "";
	private static final String TRACE_ID = "trace";

	private TraceVisualizer() {
	}

	public static Graph visualize(final Trace<?, ?> trace) {
		final Graph graph = new Graph(TRACE_ID, TRACE_LABEL);

		for (int i = 0; i < trace.getStates().size(); ++i) {
			final NodeAttributes nAttributes = NodeAttributes.builder().label(trace.getState(i).toString())
					.fillColor(FILL_COLOR).lineColor(LINE_COLOR).lineStyle(LINE_STYLE).build();
			graph.addNode(STATE_ID_PREFIX + i, nAttributes);
		}

		for (int i = 0; i < trace.getActions().size(); ++i) {
			final EdgeAttributes eAttributes = EdgeAttributes.builder().label(trace.getAction(i).toString())
					.color(LINE_COLOR).lineStyle(LINE_STYLE).build();
			graph.addEdge(STATE_ID_PREFIX + i, STATE_ID_PREFIX + (i + 1), eAttributes);
		}

		return graph;
	}
}
