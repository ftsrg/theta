package hu.bme.mit.theta.splittingcegar.common.steps;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

/**
 * Base class for the steps of the CEGAR algorithms.
 */
public class AbstractCEGARStep {
	protected final Logger logger; // Logger
	protected final Visualizer visualizer; // Visualizer
	protected final SolverWrapper solvers;
	protected final StopHandler stopHandler;

	public AbstractCEGARStep(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer) {
		this.logger = logger == null ? new NullLogger() : logger;
		this.visualizer = visualizer == null ? new NullVisualizer() : visualizer;
		this.solvers = solvers;
		this.stopHandler = stopHandler;
	}
}
