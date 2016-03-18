package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.utils;

import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Node;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

import java.util.Set;

/**
 * Helper class for converting an (interpolated) abstract Kripke structure
 * into a general graph representation that a visualizer can draw.
 * @author Akos
 */
public class VisualizationHelper {
	/**
	 * Convert an interpolated abstract Kripke structure into a graph
	 * @param system Interpolated abstract system
	 * @param exploredStates Set of explored states
	 * @param counterExample Counterexample states or null
	 * @param visualizer Visualizer
	 * @param level Minimal level of logging
	 */
	public static void visualizeAbstractKripkeStructure(InterpolatedAbstractSystem system,
			Set<InterpolatedAbstractState> exploredStates,
			IVisualizer visualizer, int level){
		
		if(level > visualizer.getMinLevel()) return;

		Graph g = new Graph("KS", "KS");
		
		// Loop through all states of the Kripke structure
		for(InterpolatedAbstractState s0 : system.getAbstractKripkeStructure().getStates()){
			StringBuilder labelString = new StringBuilder("");
			for(Expr<? extends Type> label : s0.getLabels()) labelString.append(label).append("\n");
			// Set color
			String color = ""; // Not explored
			if(s0.isPartOfCounterexample()) color = "red"; // Explored and counterexample
			else if(exploredStates.contains(s0)) color = "gray"; // Explored but not counterexample
			// Create node for state
			Node n = new Node("s_" + s0.createId(), labelString.toString(), "", color, "", s0.isInitial());
			g.addNode(n);
			// Add arcs for successor states
			for(InterpolatedAbstractState s1 : s0.getSuccessors()) n.addSuccessor("s_" + s1.createId(), "");
		}
		
		visualizer.visualize(g);
	}
}
