package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractConcretizer;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Concretizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;

public class ClusteredConcretizer extends AbstractConcretizer implements Concretizer<ClusteredAbstractSystem, ClusteredAbstractState> {

	public ClusteredConcretizer(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public ConcreteTrace concretize(final ClusteredAbstractSystem system, final List<ClusteredAbstractState> abstractCounterEx) {
		return super.concretize(system, abstractCounterEx, null, system.getVars());
	}

	@Override
	public String toString() {
		return "";
	}
}
