package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.CEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.GenericCEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.InterpolatingChecker;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.InterpolatingConcretizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.InterpolatingInitializer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.InterpolatingRefiner;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement.CraigInterpolater;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement.Interpolater;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement.SequenceInterpolater;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.utils.InterpolatingCEGARDebugger;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;

public class InterpolatingCEGARBuilder implements CEGARBuilder {
	private Logger logger = new NullLogger();
	private Visualizer visualizer = new NullVisualizer();
	private boolean collectFromConditions = false;
	private boolean collectFromSpecification = false;
	private InterpolationMethod interpolationMethod = InterpolationMethod.Craig;
	private boolean incrementalModelChecking = true;
	private boolean useCNFTransformation = false;
	private final List<String> explicitVariables = new ArrayList<>();
	private InterpolatingCEGARDebugger debugger = null;

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
		if (visualizer == null)
			this.debugger = null;
		else
			this.debugger = new InterpolatingCEGARDebugger(visualizer);
		return this;
	}

	@Override
	public GenericCEGARLoop<InterpolatedAbstractSystem, InterpolatedAbstractState> build() {
		Interpolater interpolater = null;
		switch (interpolationMethod) {
		case Craig:
			interpolater = new CraigInterpolater(logger, visualizer);
			break;
		case Sequence:
			interpolater = new SequenceInterpolater(logger, visualizer);
			break;
		default:
			throw new RuntimeException("Unknown interpolation method: " + interpolationMethod);
		}

		return new GenericCEGARLoop<>(
				new InterpolatingInitializer(logger, visualizer, collectFromConditions, collectFromSpecification, useCNFTransformation, explicitVariables),
				new InterpolatingChecker(logger, visualizer, incrementalModelChecking), new InterpolatingConcretizer(logger, visualizer),
				new InterpolatingRefiner(logger, visualizer, interpolater), debugger, logger, "Interpolating");
	}
}
