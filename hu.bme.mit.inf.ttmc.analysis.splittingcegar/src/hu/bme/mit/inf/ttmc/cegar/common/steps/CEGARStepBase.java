package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Base class for the steps of the CEGAR algorithms, contains common data.
 *
 * @author Akos
 */
public class CEGARStepBase implements IStoppable {
	protected Logger logger; // Logger
	protected IVisualizer visualizer; // Visualizer
	protected STSManager manager;
	protected Solver solver;

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
	public CEGARStepBase(final STSManager manager, final Logger logger, final IVisualizer visualizer) {
		this.manager = manager;
		this.solver = manager.getSolverFactory().createSolver(true, false);
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
