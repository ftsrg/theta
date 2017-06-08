package hu.bme.mit.theta.splittingcegar.visible.data;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractSystemBase;

/**
 * Represents the visibility-based abstract system.
 */
public class VisibleAbstractSystem extends AbstractSystemBase {
	private final Set<VarDecl<?>> visibleVars;
	private final Set<VarDecl<?>> invisibleVars;
	private final Set<VarDecl<?>> cnfVars;

	public VisibleAbstractSystem(final STS system) {
		super(system);
		visibleVars = new HashSet<>();
		invisibleVars = new HashSet<>();
		cnfVars = new HashSet<>();
	}

	public Set<VarDecl<?>> getVisibleVars() {
		return visibleVars;
	}

	public Set<VarDecl<?>> getInvisibleVars() {
		return invisibleVars;
	}

	public Set<VarDecl<?>> getCNFVars() {
		return this.cnfVars;
	}

	public void makeVisible(final VarDecl<?> var) {
		if (invisibleVars.remove(var)) {
			visibleVars.add(var);
		} else {
			throw new RuntimeException("Variable " + var + " could not be made visible because it was not found.");
		}
	}
}
