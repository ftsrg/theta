package hu.bme.mit.theta.splittingcegar.visible;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.splittingcegar.common.CEGARBuilder;
import hu.bme.mit.theta.splittingcegar.common.GenericCEGARLoop;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractState;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractSystem;
import hu.bme.mit.theta.splittingcegar.visible.steps.VisibleChecker;
import hu.bme.mit.theta.splittingcegar.visible.steps.VisibleConcretizer;
import hu.bme.mit.theta.splittingcegar.visible.steps.VisibleInitializer;
import hu.bme.mit.theta.splittingcegar.visible.steps.VisibleRefiner;
import hu.bme.mit.theta.splittingcegar.visible.steps.refinement.CraigItpVarCollector;
import hu.bme.mit.theta.splittingcegar.visible.steps.refinement.SeqItpVarCollector;
import hu.bme.mit.theta.splittingcegar.visible.steps.refinement.UnsatCoreVarCollector;
import hu.bme.mit.theta.splittingcegar.visible.steps.refinement.VarCollector;
import hu.bme.mit.theta.splittingcegar.visible.utils.VisibleCEGARDebugger;

public class VisibleCEGARBuilder implements CEGARBuilder {
	private Logger logger = new NullLogger();
	private Visualizer visualizer = new NullVisualizer();
	private boolean useCNFTransformation = false;
	private VarCollectionMethod varCollMethod = VarCollectionMethod.CraigItp;
	private Visualizer debugVisualizer = null;

	public enum VarCollectionMethod {
		CraigItp, SequenceItp, UnsatCore
	};

	public VisibleCEGARBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public VisibleCEGARBuilder visualizer(final Visualizer visualizer) {
		this.visualizer = visualizer;
		return this;
	}

	public VisibleCEGARBuilder useCNFTransformation(final boolean useCNFTransformation) {
		this.useCNFTransformation = useCNFTransformation;
		return this;
	}

	public VisibleCEGARBuilder varCollectionMethod(final VarCollectionMethod method) {
		this.varCollMethod = method;
		return this;
	}

	public VisibleCEGARBuilder debug(final Visualizer visualizer) {
		this.debugVisualizer = visualizer;
		return this;
	}

	@Override
	public GenericCEGARLoop<VisibleAbstractSystem, VisibleAbstractState> build() {
		final SolverFactory factory = Z3SolverFactory.getInstace();
		final SolverWrapper solvers = new SolverWrapper(factory.createSolver(), factory.createItpSolver());
		final StopHandler stopHandler = new StopHandler();
		VisibleCEGARDebugger debugger = null;
		if (debugVisualizer != null)
			debugger = new VisibleCEGARDebugger(solvers, debugVisualizer);
		VarCollector varCollector = null;
		switch (varCollMethod) {
		case CraigItp:
			varCollector = new CraigItpVarCollector(solvers, stopHandler, logger, visualizer);
			break;
		case SequenceItp:
			varCollector = new SeqItpVarCollector(solvers, stopHandler, logger, visualizer);
			break;
		case UnsatCore:
			varCollector = new UnsatCoreVarCollector(solvers, stopHandler, logger, visualizer);
			break;
		default:
			throw new RuntimeException("Unknown variable collection method: " + varCollMethod);
		}
		return new GenericCEGARLoop<>(solvers, stopHandler,
				new VisibleInitializer(solvers, stopHandler, logger, visualizer, useCNFTransformation),
				new VisibleChecker(solvers, stopHandler, logger, visualizer),
				new VisibleConcretizer(solvers, stopHandler, logger, visualizer),
				new VisibleRefiner(solvers, stopHandler, logger, visualizer, varCollector), debugger, logger,
				"Visible");
	}
}
