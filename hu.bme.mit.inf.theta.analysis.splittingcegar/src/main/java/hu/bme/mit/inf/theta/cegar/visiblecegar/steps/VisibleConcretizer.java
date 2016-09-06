package hu.bme.mit.inf.theta.cegar.visiblecegar.steps;

import java.util.List;

import hu.bme.mit.inf.theta.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.theta.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.theta.cegar.common.data.StopHandler;
import hu.bme.mit.inf.theta.cegar.common.steps.AbstractConcretizer;
import hu.bme.mit.inf.theta.cegar.common.steps.Concretizer;
import hu.bme.mit.inf.theta.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.theta.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.theta.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.theta.common.logging.Logger;

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
