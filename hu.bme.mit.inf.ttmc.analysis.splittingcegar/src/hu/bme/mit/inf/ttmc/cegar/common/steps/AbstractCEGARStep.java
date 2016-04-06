package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;

/**
 * Base class for the steps of the CEGAR algorithms.
 */
public class AbstractCEGARStep implements Stoppable {
	protected final Logger logger; // Logger
	protected final Visualizer visualizer; // Visualizer

	protected volatile boolean isStopped;

	@Override
	public void stop() {
		isStopped = true;
	}

	@Override
	public void resetStop() {
		isStopped = false;
	}

	public AbstractCEGARStep(final Logger logger, final Visualizer visualizer) {
		this.logger = logger == null ? new NullLogger() : logger;
		this.visualizer = visualizer == null ? new NullVisualizer() : visualizer;
		this.isStopped = false;
	}
}
