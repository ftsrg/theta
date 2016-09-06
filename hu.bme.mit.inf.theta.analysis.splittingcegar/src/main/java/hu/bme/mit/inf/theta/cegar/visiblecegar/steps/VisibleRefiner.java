package hu.bme.mit.inf.theta.cegar.visiblecegar.steps;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.theta.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.theta.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.theta.cegar.common.data.StopHandler;
import hu.bme.mit.inf.theta.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.theta.cegar.common.steps.Refiner;
import hu.bme.mit.inf.theta.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.theta.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.theta.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.theta.cegar.visiblecegar.steps.refinement.VarCollector;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;

public class VisibleRefiner extends AbstractCEGARStep implements Refiner<VisibleAbstractSystem, VisibleAbstractState> {
	private final VarCollector varCollector;

	public VisibleRefiner(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer,
			final VarCollector varCollector) {
		super(solvers, stopHandler, logger, visualizer);
		this.varCollector = checkNotNull(varCollector);
	}

	@Override
	public VisibleAbstractSystem refine(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		assert (1 <= concreteTrace.size() && concreteTrace.size() < abstractCounterEx.size());
		logger.writeln("Failure state: " + abstractCounterEx.get(concreteTrace.size() - 1), 4, 0);
		final Collection<VarDecl<? extends Type>> varsToBeMadeVisible = varCollector.collectVars(system, abstractCounterEx, concreteTrace);
		logger.write("New visible variables:", 2);
		final int previouslyVisibleVarCount = system.getVisibleVars().size();
		for (final VarDecl<? extends Type> var : varsToBeMadeVisible) {
			if (!system.getVisibleVars().contains(var)) {
				system.makeVisible(var);
				logger.write(" " + var, 2);
			}
		}
		logger.writeln(2);
		assert (previouslyVisibleVarCount < system.getVisibleVars().size());
		assert (system.getVisibleVars().size() + system.getInvisibleVars().size() == system.getVars().size());
		return system;
	}

	@Override
	public String toString() {
		return varCollector.toString();
	}
}
