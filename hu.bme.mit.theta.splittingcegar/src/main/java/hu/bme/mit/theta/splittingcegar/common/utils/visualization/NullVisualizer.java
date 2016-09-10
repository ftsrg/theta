package hu.bme.mit.theta.splittingcegar.common.utils.visualization;

import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Graph;

/**
 * Null visualizer, does nothing
 * @author Akos
 */
public class NullVisualizer implements Visualizer {

	@Override
	public int getMinLevel() { return -1; }

	@Override
	public String visualize(Graph graph) { return null; }

}
