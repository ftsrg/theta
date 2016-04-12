package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractConcretizer;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Concretizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;

public class InterpolatingConcretizer extends AbstractConcretizer implements Concretizer<InterpolatedAbstractSystem, InterpolatedAbstractState> {

	public InterpolatingConcretizer(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public ConcreteTrace concretize(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx) {
		final NotExpr negSpec = system.getManager().getExprFactory().Not(system.getSTS().getProp());
		return super.concretize(system, abstractCounterEx, negSpec, system.getVars());
	}

	@Override
	public String toString() {
		return "";
	}
}
