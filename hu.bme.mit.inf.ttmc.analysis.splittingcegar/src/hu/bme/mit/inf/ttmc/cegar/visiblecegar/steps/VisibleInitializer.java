package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Initializer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSCNFTransformation;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSITETransformation;

/**
 * Loads system and collects the initially visible/invisible variables based on
 * the specification expression.
 *
 * @author Akos
 */
public class VisibleInitializer extends AbstractCEGARStep implements Initializer<VisibleAbstractSystem> {

	private final boolean useCNFTransformation;

	/**
	 * Initialize the step with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 */
	public VisibleInitializer(final Logger logger, final Visualizer visualizer, final boolean useCNFTransformation) {
		super(logger, visualizer);
		this.useCNFTransformation = useCNFTransformation;
	}

	@Override
	public VisibleAbstractSystem create(STS concrSys) {
		logger.write("Variables [" + concrSys.getVars().size() + "]:", 2);
		for (final VarDecl<? extends Type> varDecl : concrSys.getVars())
			logger.write(" " + varDecl.getName(), 3);
		logger.writeln(2);

		logger.writeln("Specification expression: " + concrSys.getProp(), 2);

		// Eliminate if-then-else expressions from the constraints by replacing them with implications
		logger.write("Eliminating if-then-else expressions from the constraints...", 3);
		concrSys = new STSITETransformation().transform(concrSys);
		logger.writeln("done.", 3);

		final List<VarDecl<? extends Type>> visibleVars = new ArrayList<>();
		final List<VarDecl<? extends Type>> invisibleVars = new ArrayList<>(concrSys.getVars()); // First assume that each variable is invisible
		final List<VarDecl<? extends Type>> cnfVars = new ArrayList<>();
		final List<VarDecl<? extends Type>> nonCnfVars = new ArrayList<>(concrSys.getVars());

		// Then make variables appearing in the specification visible
		for (final VarDecl<? extends Type> varDec : FormalismUtils.collectVars(concrSys.getProp()))
			if (!visibleVars.contains(varDec)) {
				invisibleVars.remove(varDec);
				visibleVars.add(varDec);
			}
		// Check if each variable belongs somewhere
		assert (visibleVars.size() + invisibleVars.size() == concrSys.getVars().size());
		// Print visible variables
		logger.write("Visible variables [" + visibleVars.size() + "]:", 2);
		for (final VarDecl<? extends Type> varDec : visibleVars)
			logger.write(" " + varDec.getName(), 2);
		logger.writeln(2);

		// Apply CNF transformation if needed
		if (useCNFTransformation) {
			logger.write("Transforming constraints to CNF...", 3);
			concrSys = new STSCNFTransformation().transform(concrSys);
			// Collect the new helper variables
			for (final VarDecl<? extends Type> varDecl : concrSys.getVars()) {
				if (!nonCnfVars.contains(varDecl))
					cnfVars.add(varDecl);
			}
			// # normal variables + # new variables == # all variables
			assert (nonCnfVars.size() + cnfVars.size() == concrSys.getVars().size());
			logger.writeln("done, " + cnfVars.size() + " new variables were added.", 3);
		}

		final VisibleAbstractSystem system = new VisibleAbstractSystem(concrSys);
		system.getVars().addAll(nonCnfVars);
		system.getCNFVariables().addAll(cnfVars);
		system.getVisibleVariables().addAll(visibleVars);
		system.getInvisibleVariables().addAll(invisibleVars);

		assert (system.getInvisibleVariables().size() + system.getVisibleVariables().size() == system.getVars().size());
		assert (system.getVars().size() + system.getCNFVariables().size() == system.getSTS().getVars().size());

		return system;
	}

	@Override
	public String toString() {
		return useCNFTransformation ? "CNF" : "";
	}
}
