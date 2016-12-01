package hu.bme.mit.theta.splittingcegar.common.utils.visualization;

import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Graph;

/**
 * Visualizer interface
 * @author Akos
 */
public interface Visualizer {	
	
	/**
	 * Visualize a graph
	 * @param graph Graph
	 * @return Name of the generated file, or null
	 */
	String visualize(Graph graph);
	
	/**
	 * Get the minimal level of logging
	 * @return Level of logging
	 */
	int getMinLevel();
}
