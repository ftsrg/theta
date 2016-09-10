package hu.bme.mit.theta.splittingcegar.clustered.steps;

import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractSystem;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractConcretizer;
import hu.bme.mit.theta.splittingcegar.common.steps.Concretizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

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
