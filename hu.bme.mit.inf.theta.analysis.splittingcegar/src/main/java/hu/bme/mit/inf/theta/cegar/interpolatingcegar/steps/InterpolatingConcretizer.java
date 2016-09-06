package hu.bme.mit.inf.theta.cegar.interpolatingcegar.steps;

import java.util.List;

import hu.bme.mit.inf.theta.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.theta.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.theta.cegar.common.data.StopHandler;
import hu.bme.mit.inf.theta.cegar.common.steps.AbstractConcretizer;
import hu.bme.mit.inf.theta.cegar.common.steps.Concretizer;
import hu.bme.mit.inf.theta.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.theta.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.theta.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.core.expr.NotExpr;
import hu.bme.mit.inf.theta.core.expr.impl.Exprs;

public class InterpolatingConcretizer extends AbstractConcretizer implements Concretizer<InterpolatedAbstractSystem, InterpolatedAbstractState> {

	public InterpolatingConcretizer(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public ConcreteTrace concretize(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx) {
		final NotExpr negSpec = Exprs.Not(system.getSTS().getProp());
		return super.concretize(system, abstractCounterEx, negSpec, system.getVars());
	}

	@Override
	public String toString() {
		return "";
	}
}
