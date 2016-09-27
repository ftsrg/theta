package hu.bme.mit.theta.splittingcegar.clustered;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractSystem;
import hu.bme.mit.theta.splittingcegar.clustered.steps.ClusteredChecker;
import hu.bme.mit.theta.splittingcegar.clustered.steps.ClusteredConcretizer;
import hu.bme.mit.theta.splittingcegar.clustered.steps.ClusteredInitializer;
import hu.bme.mit.theta.splittingcegar.clustered.steps.ClusteredRefiner;
import hu.bme.mit.theta.splittingcegar.clustered.utils.ClusteredCEGARDebugger;
import hu.bme.mit.theta.splittingcegar.common.CEGARBuilder;
import hu.bme.mit.theta.splittingcegar.common.GenericCEGARLoop;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

public class ClusteredCEGARBuilder implements CEGARBuilder {
	private Logger logger = new NullLogger();
	private Visualizer visualizer = new NullVisualizer();
	private Visualizer debugVisualizer = null;

	public ClusteredCEGARBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public ClusteredCEGARBuilder visualizer(final Visualizer visualizer) {
		this.visualizer = visualizer;
		return this;
	}

	public ClusteredCEGARBuilder debug(final Visualizer visualizer) {
		this.debugVisualizer = visualizer;
		return this;
	}

	@Override
	public GenericCEGARLoop<ClusteredAbstractSystem, ClusteredAbstractState> build() {
		final SolverManager manager = new Z3SolverManager();
		final SolverWrapper solvers = new SolverWrapper(manager.createSolver(), manager.createItpSolver());
		final StopHandler stopHandler = new StopHandler();
		ClusteredCEGARDebugger debugger = null;
		if (debugVisualizer != null)
			debugger = new ClusteredCEGARDebugger(solvers, debugVisualizer);
		return new GenericCEGARLoop<>(solvers, stopHandler,
				new ClusteredInitializer(solvers, stopHandler, logger, visualizer),
				new ClusteredChecker(solvers, stopHandler, logger, visualizer),
				new ClusteredConcretizer(solvers, stopHandler, logger, visualizer),
				new ClusteredRefiner(solvers, stopHandler, logger, visualizer), debugger, logger, "Clustered");
	}
}
