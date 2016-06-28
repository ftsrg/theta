package hu.bme.mit.inf.ttmc.cegar.visiblecegar;

import hu.bme.mit.inf.ttmc.cegar.common.CEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.GenericCEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.ttmc.cegar.common.data.StopHandler;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleChecker;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleConcretizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleInitializer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleRefiner;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.CraigItpVarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.SeqItpVarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.UnsatCoreVarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.VarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.utils.VisibleCEGARDebugger;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

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
		final SolverManager manager = new Z3SolverManager();
		final SolverWrapper solvers = new SolverWrapper(manager.createSolver(true, true), manager.createItpSolver());
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
