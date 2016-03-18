package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.NullLogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Base class for the steps of the CEGAR algorithms, contains common data.
 *
 * @author Akos
 */
public class CEGARStepBase {
	protected ILogger logger; // Logger
	protected IVisualizer visualizer; // Visualizer
	protected STSManager manager;
	protected Solver solver;

	/**
	 * Initialize step with a manager, logger and visualizer
	 * 
	 * @param manager
	 * @param logger
	 * @param visualizer
	 */
	public CEGARStepBase(final STSManager manager, final ILogger logger, final IVisualizer visualizer) {
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
	}
}
