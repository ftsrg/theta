package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IRefiner;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.IVariableCollector;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public class VisibleRefiner extends CEGARStepBase implements IRefiner<VisibleAbstractSystem, VisibleAbstractState> {
	private final IVariableCollector variableCollector;

	/**
	 * Initialize the step with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 */
	public VisibleRefiner(final STSManager manager, final ILogger logger, final IVisualizer visualizer, final IVariableCollector variableCollector) {
		super(manager, logger, visualizer);
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
		assert (system.getVisibleVariables().size() + system.getInvisibleVariables().size() == system.getVariables().size());
		return system;
	}

	@Override
	public String toString() {
		return variableCollector.toString();
	}
}
