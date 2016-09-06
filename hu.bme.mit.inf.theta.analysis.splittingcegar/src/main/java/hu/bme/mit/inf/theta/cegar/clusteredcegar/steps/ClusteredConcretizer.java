package hu.bme.mit.inf.theta.cegar.clusteredcegar.steps;

import java.util.List;

import hu.bme.mit.inf.theta.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.theta.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.theta.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.theta.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.theta.cegar.common.data.StopHandler;
import hu.bme.mit.inf.theta.cegar.common.steps.AbstractConcretizer;
import hu.bme.mit.inf.theta.cegar.common.steps.Concretizer;
import hu.bme.mit.inf.theta.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.theta.common.logging.Logger;

public class ClusteredConcretizer extends AbstractConcretizer implements Concretizer<ClusteredAbstractSystem, ClusteredAbstractState> {

	public ClusteredConcretizer(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
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
