package hu.bme.mit.inf.ttmc.cegar.visiblecegar.data;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystemBase;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Represents the visibility-based abstract system.
 *
 * @author Akos
 */
public class VisibleAbstractSystem extends AbstractSystemBase {
	private final Set<VarDecl<? extends Type>> visibleVariables;
	private final Set<VarDecl<? extends Type>> invisibleVariables;
	private final Set<VarDecl<? extends Type>> cnfVariables;

	/**
	 * Constructor
	 *
	 * @param problem
	 *            Problem
	 */
	public VisibleAbstractSystem(final STS system) {
		super(system);
		visibleVariables = new HashSet<>();
		invisibleVariables = new HashSet<>();
		cnfVariables = new HashSet<>();
	}

	/**
	 * Get the list of visible variables
	 *
	 * @return List of visible variables
	 */
	public Set<VarDecl<? extends Type>> getVisibleVariables() {
		return visibleVariables;
	}

	/**
	 * Get the list of invisible variables
	 *
	 * @return List of invisible variables
	 */
	public Set<VarDecl<? extends Type>> getInvisibleVariables() {
		return invisibleVariables;
	}

	/**
	 * Get the list of variables introduced by the CNF (Tseitin) transformation
	 *
	 * @return List of CNF variables
	 */
	public Set<VarDecl<? extends Type>> getCNFVariables() {
		return this.cnfVariables;
	}

	/**
	 * Make a previously invisible variable visible
	 *
	 * @param variable
	 */
	public void makeVisible(final VarDecl<? extends Type> variable) {
		if (invisibleVariables.remove(variable)) {
			visibleVariables.add(variable);
		} else
			throw new RuntimeException("Variable " + variable + " could not be made visible because it was not found.");
	}
}
