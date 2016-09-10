package hu.bme.mit.theta.splittingcegar.visible.steps;

import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractConcretizer;
import hu.bme.mit.theta.splittingcegar.common.steps.Concretizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractState;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractSystem;

public class VisibleConcretizer extends AbstractConcretizer implements Concretizer<VisibleAbstractSystem, VisibleAbstractState> {

	public VisibleConcretizer(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
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
