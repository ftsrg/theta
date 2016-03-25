package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractConcretizer;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Concretizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;

/**
 * Tries to find a concrete counterexample for an abstract counterexample. If no
 * concrete counterexample exists, then it finds the longest prefix of the
 * abstract counterexample for which a concrete trace exists.
 *
 * @author Akos
 */
public class VisibleConcretizer extends AbstractConcretizer implements Concretizer<VisibleAbstractSystem, VisibleAbstractState> {

	public VisibleConcretizer(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public ConcreteTrace concretize(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx) {
		return super.concretize(system, abstractCounterEx, null, system.getVars());
	}

	@Override
	public String toString() {
		return "";
	}
}
