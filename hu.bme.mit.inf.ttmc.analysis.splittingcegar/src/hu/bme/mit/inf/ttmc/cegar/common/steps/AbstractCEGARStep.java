package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.ttmc.cegar.common.data.StopHandler;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;

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
