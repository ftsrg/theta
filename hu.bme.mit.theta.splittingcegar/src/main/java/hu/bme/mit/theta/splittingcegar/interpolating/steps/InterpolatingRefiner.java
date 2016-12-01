package hu.bme.mit.theta.splittingcegar.interpolating.steps;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.steps.Refiner;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.interpolating.data.Interpolant;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement.CounterexampleSplitter;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement.Interpolater;
import hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement.Splitter;

public class InterpolatingRefiner extends AbstractCEGARStep implements Refiner<InterpolatedAbstractSystem, InterpolatedAbstractState> {

	private final Interpolater interpolater;
	private final Splitter splitter;

	public InterpolatingRefiner(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer,
			final Interpolater interpolater) {
		super(solvers, stopHandler, logger, visualizer);
		this.interpolater = checkNotNull(interpolater);
		this.splitter = new CounterexampleSplitter(solvers, stopHandler, logger, visualizer);

	}

	@Override
	public InterpolatedAbstractSystem refine(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		final int traceLength = concreteTrace.size();
		assert (1 <= traceLength && traceLength <= abstractCounterEx.size());

		final InterpolatedAbstractState failureState = abstractCounterEx.get(traceLength - 1);
		logger.writeln("Failure state: " + failureState, 4, 0);

		// Get interpolant (binary or sequence)
		final Interpolant interpolant = interpolater.interpolate(system, abstractCounterEx, concreteTrace);
		logger.writeln("Interpolant: " + interpolant, 2, 0);

		if (stopHandler.isStopped())
			return null;

		// Split state(s)
		final int states = system.getAbstractKripkeStructure().getStates().size();
		final int firstSplit = splitter.split(system, abstractCounterEx, interpolant);

		if (stopHandler.isStopped())
			return null;

		assert (states < system.getAbstractKripkeStructure().getStates().size());

		// Set the index of the split state, i.e., the index of the first state
		// in the abstract counterexample that was split (for incremental model checking)
		system.setPreviousSplitIndex(firstSplit);

		// Clear counterexample markers
		for (final InterpolatedAbstractState as : abstractCounterEx)
			as.setPartOfCounterexample(false);

		return system;
	}

	@Override
	public String toString() {
		return interpolater.toString();
	}
}
