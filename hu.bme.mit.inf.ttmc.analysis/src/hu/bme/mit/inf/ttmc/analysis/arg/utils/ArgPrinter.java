package hu.bme.mit.inf.ttmc.analysis.arg.utils;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.arg.ArgState;

public class ArgPrinter {

	private ArgPrinter() {

	}

	public static <S extends State> String toGraphvizString(final Collection<ArgState<S>> states) {
		final Set<ArgState<S>> allStates = new HashSet<>();

		for (final ArgState<S> state : states) {
			allStates.add(state);
			allStates.addAll(state.getSuccessors());
		}

		final Map<ArgState<S>, String> ids = createStateIds(allStates);

		final StringBuilder sb = new StringBuilder();
		sb.append("digraph statespace {\n");
		for (final ArgState<S> state : allStates) {

			if (state.isStart().isPresent() && state.isStart().get()) {
				sb.append("\ti").append(ids.get(state)).append(" [style=invis]\n");
				sb.append("\t\ti").append(ids.get(state)).append(" -> ").append(ids.get(state)).append("\n");
			}

			sb.append("\t").append(ids.get(state)).append(" [label=\"").append(state.getState().toString()).append("\"");
			if (state.isTarget().isPresent() && state.isTarget().get())
				sb.append(",peripheries=2");
			sb.append("]\n");

			for (final ArgState<S> succ : state.getSuccessors()) {
				sb.append("\t\t").append(ids.get(state)).append(" -> ").append(ids.get(succ)).append("\n");
			}
		}
		sb.append("}");
		return sb.toString();
	}

	private static <S extends State> Map<ArgState<S>, String> createStateIds(final Collection<ArgState<S>> states) {
		final Map<ArgState<S>, String> ids = new HashMap<>();
		int id = 0;
		for (final ArgState<S> state : states) {
			ids.put(state, Integer.toString(id));
			++id;
		}

		return ids;
	}
}
