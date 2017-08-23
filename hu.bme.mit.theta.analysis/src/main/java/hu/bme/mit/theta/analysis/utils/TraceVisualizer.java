package hu.bme.mit.theta.analysis.utils;

import java.awt.Color;
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
}
