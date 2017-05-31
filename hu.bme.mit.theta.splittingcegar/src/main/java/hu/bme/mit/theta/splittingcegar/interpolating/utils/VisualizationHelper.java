package hu.bme.mit.theta.splittingcegar.interpolating.utils;

import java.util.Set;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Node;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;

/**
 * Helper class for converting an (interpolated) abstract Kripke structure into
 * a general graph representation that a visualizer can draw.
 * 
 * @author Akos
 */
public class VisualizationHelper {
	/**
	 * Convert an interpolated abstract Kripke structure into a graph
	 * 
	 * @param system
	 *            Interpolated abstract system
	 * @param exploredStates
	 *            Set of explored states
	 * @param counterExample
	 *            Counterexample states or null
	 * @param visualizer
	 *            Visualizer
	 * @param level
	 *            Minimal level of logging
	 */
	public static void visualizeAbstractKripkeStructure(final InterpolatedAbstractSystem system,
			final Set<InterpolatedAbstractState> exploredStates, final Visualizer visualizer, final int level) {

		if (level > visualizer.getMinLevel())
			return;

		final Graph g = new Graph("KS", "KS");

		// Loop through all states of the Kripke structure
		for (final InterpolatedAbstractState s0 : system.getAbstractKripkeStructure().getStates()) {
			final StringBuilder labelString = new StringBuilder("");
			for (final Expr<?> label : s0.getLabels())
				labelString.append(label).append("\n");
			// Set color
			String color = ""; // Not explored
			if (s0.isPartOfCounterexample())
				color = "red"; // Explored and counterexample
			else if (exploredStates.contains(s0))
				color = "gray"; // Explored but not counterexample
			// Create node for state
			final Node n = new Node("s_" + s0.createId(), labelString.toString(), "", color, "", s0.isInitial());
			g.addNode(n);
			// Add arcs for successor states
			for (final InterpolatedAbstractState s1 : s0.getSuccessors())
				n.addSuccessor("s_" + s1.createId(), "");
		}

		visualizer.visualize(g);
	}
}
