package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;

/**
 * Base class for the steps of the CEGAR algorithms, contains common data.
 *
 * @author Akos
 */
public class CEGARStepBase implements IStoppable {
	protected Logger logger; // Logger
	protected IVisualizer visualizer; // Visualizer

	protected volatile boolean isStopped;

	@Override
	public void stop() {
		isStopped = true;
	}

	@Override
	public void resetStop() {
		isStopped = false;
	}

	/**
	 * Initialize step with a manager, logger and visualizer
	 *
	 * @param manager
	 * @param logger
	 * @param visualizer
	 */
	public CEGARStepBase(final Logger logger, final IVisualizer visualizer) {
		if (logger == null)
			this.logger = new NullLogger();
		else
			this.logger = logger;
		if (visualizer == null)
			this.visualizer = new NullVisualizer();
		else
			this.visualizer = visualizer;

		this.isStopped = false;
	}
}
