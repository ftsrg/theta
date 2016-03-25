package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Refiner;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.IVarCollector;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class VisibleRefiner extends AbstractCEGARStep implements Refiner<VisibleAbstractSystem, VisibleAbstractState> {
	private final IVarCollector variableCollector;

	/**
	 * Initialize the step with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 */
	public VisibleRefiner(final Logger logger, final Visualizer visualizer, final IVarCollector variableCollector) {
		super(logger, visualizer);
		this.variableCollector = variableCollector;
	}

	@Override
	public VisibleAbstractSystem refine(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		assert (1 <= concreteTrace.size() && concreteTrace.size() < abstractCounterEx.size());
		logger.writeln("Failure state: " + abstractCounterEx.get(concreteTrace.size() - 1), 4, 0);
		final Collection<VarDecl<? extends Type>> variables = variableCollector.collectVariables(system, abstractCounterEx, concreteTrace);
		logger.write("New visible variables:", 2);
		final int previouslyVisibleVariables = system.getVisibleVariables().size();
		for (final VarDecl<? extends Type> variable : variables) {
			if (!system.getVisibleVariables().contains(variable)) {
				system.makeVisible(variable);
				logger.write(" " + variable, 2);
			}
		}
		logger.writeln(2);
		assert (previouslyVisibleVariables < system.getVisibleVariables().size());
		assert (system.getVisibleVariables().size() + system.getInvisibleVariables().size() == system.getVars().size());
		return system;
	}

	@Override
	public String toString() {
		return variableCollector.toString();
	}
}
