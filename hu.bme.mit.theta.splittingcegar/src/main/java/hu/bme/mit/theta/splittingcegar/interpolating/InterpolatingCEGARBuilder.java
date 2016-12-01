package hu.bme.mit.theta.splittingcegar.interpolating;

import java.util.ArrayList;
import java.util.List;

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
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.InterpolatingChecker;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.InterpolatingConcretizer;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.InterpolatingInitializer;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.InterpolatingRefiner;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement.CraigInterpolater;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement.Interpolater;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement.SequenceInterpolater;
import hu.bme.mit.theta.splittingcegar.interpolating.utils.InterpolatingCEGARDebugger;

public class InterpolatingCEGARBuilder implements CEGARBuilder {
	private Logger logger = new NullLogger();
	private Visualizer visualizer = new NullVisualizer();
	private boolean collectFromConditions = false;
	private boolean collectFromSpecification = false;
	private InterpolationMethod interpolationMethod = InterpolationMethod.Craig;
	private boolean incrementalModelChecking = true;
	private boolean useCNFTransformation = false;
	private final List<String> explicitVariables = new ArrayList<>();
	private Visualizer debugVisualizer = null;

	public enum InterpolationMethod {
		Craig, Sequence
	};

	public InterpolatingCEGARBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public InterpolatingCEGARBuilder visualizer(final Visualizer visualizer) {
		this.visualizer = visualizer;
		return this;
	}

	public InterpolatingCEGARBuilder collectFromConditions(final boolean collectFromConditions) {
		this.collectFromConditions = collectFromConditions;
		return this;
	}

	public InterpolatingCEGARBuilder collectFromSpecification(final boolean collectFromSpecification) {
		this.collectFromSpecification = collectFromSpecification;
		return this;
	}

	public InterpolatingCEGARBuilder interpolationMethod(final InterpolationMethod interpolationMethod) {
		this.interpolationMethod = interpolationMethod;
		return this;
	}

	public InterpolatingCEGARBuilder incrementalModelChecking(final boolean incrementalModelChecking) {
		this.incrementalModelChecking = incrementalModelChecking;
		return this;
	}

	public InterpolatingCEGARBuilder useCNFTransformation(final boolean useCNFTransformation) {
		this.useCNFTransformation = useCNFTransformation;
		return this;
	}

	public InterpolatingCEGARBuilder explicitVar(final String variable) {
		this.explicitVariables.add(variable);
		return this;
	}

	public InterpolatingCEGARBuilder debug(final Visualizer visualizer) {
		this.debugVisualizer = visualizer;
		return this;
	}

	@Override
	public GenericCEGARLoop<InterpolatedAbstractSystem, InterpolatedAbstractState> build() {
		final SolverFactory factory = Z3SolverFactory.getInstace();
		final SolverWrapper solvers = new SolverWrapper(factory.createSolver(), factory.createItpSolver());
		final StopHandler stopHandler = new StopHandler();
		InterpolatingCEGARDebugger debugger = null;
		if (debugVisualizer != null)
			debugger = new InterpolatingCEGARDebugger(solvers, debugVisualizer);
		Interpolater interpolater = null;
		switch (interpolationMethod) {
		case Craig:
			interpolater = new CraigInterpolater(solvers, stopHandler, logger, visualizer);
			break;
		case Sequence:
			interpolater = new SequenceInterpolater(solvers, stopHandler, logger, visualizer);
			break;
		default:
			throw new RuntimeException("Unknown interpolation method: " + interpolationMethod);
		}

		return new GenericCEGARLoop<>(solvers, stopHandler,
				new InterpolatingInitializer(solvers, stopHandler, logger, visualizer, collectFromConditions,
						collectFromSpecification, useCNFTransformation, explicitVariables),
				new InterpolatingChecker(solvers, stopHandler, logger, visualizer, incrementalModelChecking),
				new InterpolatingConcretizer(solvers, stopHandler, logger, visualizer),
				new InterpolatingRefiner(solvers, stopHandler, logger, visualizer, interpolater), debugger, logger,
				"Interpolating");
	}
}
