package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.ConcretizerBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IConcretizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Tries to find a concrete counterexample for an abstract counterexample. If no
 * concrete counterexample exists, then it finds the longest prefix of the
 * abstract counterexample for which a concrete trace exists.
 *
 * @author Akos
 */
public class VisibleConcretizer extends ConcretizerBase implements IConcretizer<VisibleAbstractSystem, VisibleAbstractState> {

	public VisibleConcretizer(final STSManager manager, final ILogger logger, final IVisualizer visualizer) {
		super(manager, logger, visualizer);
	}

	@Override
	public ConcreteTrace concretize(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx) {
		return super.concretize(system.getUnroller(), abstractCounterEx, null, system.getVariables());
	}

	@Override
	public String toString() {
		return "";
	}
}
