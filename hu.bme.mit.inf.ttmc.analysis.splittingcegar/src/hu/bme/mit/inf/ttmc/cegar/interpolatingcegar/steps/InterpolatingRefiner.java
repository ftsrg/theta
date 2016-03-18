package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IRefiner;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.Interpolant;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement.CounterexampleSplitter;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement.IInterpolater;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement.IStateSplitter;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Refines the abstraction using the spurious counterexample.
 *
 * @author Akos
 */
public class InterpolatingRefiner extends CEGARStepBase implements IRefiner<InterpolatedAbstractSystem, InterpolatedAbstractState> {

	private final IInterpolater interpolater;

	/**
	 * Initialize the step with a solver, logger, visualizer and interpolater
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 * @param interpolater
	 */
	public InterpolatingRefiner(final STSManager manager, final ILogger logger, final IVisualizer visualizer, final IInterpolater interpolater) {
		super(manager, logger, visualizer);
		this.interpolater = interpolater;
	}

	@Override
	public InterpolatedAbstractSystem refine(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		final int traceLength = concreteTrace.size();
		assert (1 <= traceLength && traceLength <= abstractCounterEx.size());

		// The failure state is the last state in the abstract counterexample which
		// can be reached with a concrete path (or the last state if the last concrete
		// state satisfies the formula)
		final InterpolatedAbstractState failureState = abstractCounterEx.get(traceLength - 1);
		logger.writeln("Failure state: " + failureState, 4, 0);

		// Get interpolant (binary or sequence)
		final Interpolant interpolant = interpolater.interpolate(system, abstractCounterEx, concreteTrace);
		logger.writeln("Interpolant: " + interpolant, 2, 0);

		// Split state(s)
		final IStateSplitter splitter = new CounterexampleSplitter(manager, logger, visualizer);
		final int states = system.getAbstractKripkeStructure().getStates().size();
		final int firstSplit = splitter.split(system, abstractCounterEx, interpolant);
		assert (states < system.getAbstractKripkeStructure().getStates().size());

		// Set the index of the split state, i.e., the index of the first state
		// in the abstract counterexample that was split (for incremental model checking)
		system.setPreviousSplitIndex(firstSplit);

		// Clear counterexample marker
		for (final InterpolatedAbstractState as : abstractCounterEx)
			as.setPartOfCounterexample(false);

		return system;
	}

	@Override
	public String toString() {
		return interpolater.toString();
	}
}
