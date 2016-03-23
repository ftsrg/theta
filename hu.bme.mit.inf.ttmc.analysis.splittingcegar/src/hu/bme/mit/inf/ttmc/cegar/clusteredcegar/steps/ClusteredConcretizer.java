package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.ConcretizerBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IConcretizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;

/**
 * Tries to find a concrete counterexample for an abstract counterexample. If no
 * concrete counterexample exists, then it finds the longest prefix of the
 * abstract counterexample for which a concrete trace exists.
 *
 * @author Akos
 */
public class ClusteredConcretizer extends ConcretizerBase implements IConcretizer<ClusteredAbstractSystem, ClusteredAbstractState> {

	/**
	 * Initialize the step with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 */
	public ClusteredConcretizer(final Logger logger, final IVisualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public ConcreteTrace concretize(final ClusteredAbstractSystem system, final List<ClusteredAbstractState> abstractCounterEx) {
		return super.concretize(system, abstractCounterEx, null, system.getVariables());
	}

	@Override
	public String toString() {
		return "";
	}
}
