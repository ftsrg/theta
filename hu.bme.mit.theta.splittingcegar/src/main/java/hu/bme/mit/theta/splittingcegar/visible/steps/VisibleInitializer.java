package hu.bme.mit.theta.splittingcegar.visible.steps;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsCnfTransformation;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.steps.Initializer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractSystem;

public class VisibleInitializer extends AbstractCEGARStep implements Initializer<VisibleAbstractSystem> {

	private final boolean useCNFTransformation;

	public VisibleInitializer(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer, final boolean useCNFTransformation) {
		super(solvers, stopHandler, logger, visualizer);
		this.useCNFTransformation = useCNFTransformation;
	}

	@Override
	public VisibleAbstractSystem create(STS concrSys) {
		logger.write("Variables [" + concrSys.getVars().size() + "]:", 2);
		for (final VarDecl<?> varDecl : concrSys.getVars())
			logger.write(" " + varDecl.getName(), 3);
		logger.writeln(2);

		logger.writeln("Specification expression: " + concrSys.getProp(), 2);

		logger.write("Eliminating if-then-else expressions from the constraints...", 3);
		concrSys = new StsIteTransformation().transform(concrSys);
		logger.writeln("done.", 3);

		final List<VarDecl<?>> visibleVars = new ArrayList<>();
		final List<VarDecl<?>> invisibleVars = new ArrayList<>(concrSys.getVars()); // First
																					// assume
																					// that
																					// each
																					// variable
																					// is
																					// invisible
		final List<VarDecl<?>> cnfVars = new ArrayList<>();
		final List<VarDecl<?>> nonCnfVars = new ArrayList<>(concrSys.getVars());

		// Then make variables appearing in the specification visible
		for (final VarDecl<?> varDec : ExprUtils.getVars(concrSys.getProp()))
			if (!visibleVars.contains(varDec)) {
				invisibleVars.remove(varDec);
				visibleVars.add(varDec);
			}
		// Check if each variable belongs somewhere
		assert (visibleVars.size() + invisibleVars.size() == concrSys.getVars().size());
		// Print visible variables
		logger.write("Visible variables [" + visibleVars.size() + "]:", 2);
		for (final VarDecl<?> varDec : visibleVars)
			logger.write(" " + varDec.getName(), 2);
		logger.writeln(2);

		// Apply CNF transformation if needed
		if (useCNFTransformation) {
			logger.write("Transforming constraints to CNF...", 3);
			concrSys = new StsCnfTransformation().transform(concrSys);
			// Collect the new helper variables
			for (final VarDecl<?> varDecl : concrSys.getVars()) {
				if (!nonCnfVars.contains(varDecl))
					cnfVars.add(varDecl);
			}
			// # normal variables + # new variables == # all variables
			assert (nonCnfVars.size() + cnfVars.size() == concrSys.getVars().size());
			logger.writeln("done, " + cnfVars.size() + " new variables were added.", 3);
		}

		final VisibleAbstractSystem system = new VisibleAbstractSystem(concrSys);
		system.getVars().addAll(nonCnfVars);
		system.getCNFVars().addAll(cnfVars);
		system.getVisibleVars().addAll(visibleVars);
		system.getInvisibleVars().addAll(invisibleVars);

		assert (system.getInvisibleVars().size() + system.getVisibleVars().size() == system.getVars().size());
		assert (system.getVars().size() + system.getCNFVars().size() == system.getSTS().getVars().size());

		return system;
	}

	@Override
	public String toString() {
		return useCNFTransformation ? "CNF" : "";
	}
}
