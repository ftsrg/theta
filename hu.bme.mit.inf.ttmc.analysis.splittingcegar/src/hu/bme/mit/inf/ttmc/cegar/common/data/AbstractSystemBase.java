package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSUnrollerImpl;

/**
 * Base class for abstract systems. Contains common data and helper methods.
 *
 * @author Akos
 */
public abstract class AbstractSystemBase implements IAbstractSystem {
	protected STS system; // Reference to the system
	protected STSUnroller unroller;
	protected Set<VarDecl<? extends Type>> variables; // Variables of the system

	public AbstractSystemBase(final STS system) {
		this.system = system;
		this.unroller = new STSUnrollerImpl(system, system.getManager());
		this.variables = new HashSet<>();
	}

	@Override
	public STS getSystem() {
		return system;
	}

	@Override
	public Set<VarDecl<? extends Type>> getVariables() {
		return variables;
	}

	@Override
	public STSUnroller getUnroller() {
		return unroller;
	}

	@Override
	public STSManager getManager() {
		return system.getManager();
	}
}
