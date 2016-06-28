package hu.bme.mit.inf.ttmc.cegar.visiblecegar.utils;

import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Node;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;

import java.util.Collection;

/**
 * Helper class for converting an (visible variable-based) abstract Kripke structure
 * into a general graph representation that a visualizer can draw.
 * @author Akos
 */
public class VisualizationHelper {

	public static void visualize(Collection<VisibleAbstractState> exploredStates, Visualizer visualizer, int level) {
		if(level > visualizer.getMinLevel()) return;
		
		Graph g = new Graph("KS", "KS");
		
		// Loop through explored states
		for (VisibleAbstractState vas0 : exploredStates) {
			Node n = new Node("s_" + vas0.createId(), vas0.getValuation().toString(), "",
					vas0.isPartOfCounterexample() ? "red" : "", "", vas0.isInitial());
			g.addNode(n);
			for (VisibleAbstractState vas1 : vas0.getSuccessors()) n.addSuccessor("s_" + vas1.createId(), "");
		}
		visualizer.visualize(g);
	}
}
