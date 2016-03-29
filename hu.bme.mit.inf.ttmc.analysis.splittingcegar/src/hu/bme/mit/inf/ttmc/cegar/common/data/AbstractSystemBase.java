package hu.bme.mit.inf.ttmc.cegar.common.data;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSUnrollerImpl;

/**
 * Base class for abstract systems.
 */
public abstract class AbstractSystemBase implements AbstractSystem {
	protected STS sts;
	protected STSUnroller unroller;
	protected Set<VarDecl<? extends Type>> vars;

	public AbstractSystemBase(final STS sts) {
		this.sts = checkNotNull(sts);
		this.unroller = new STSUnrollerImpl(sts, sts.getManager());
		this.vars = new HashSet<>();
	}

	@Override
	public STS getSTS() {
		return sts;
	}

	@Override
	public Set<VarDecl<? extends Type>> getVars() {
		return vars;
	}

	@Override
	public STSUnroller getUnroller() {
		return unroller;
	}

	@Override
	public STSManager getManager() {
		return sts.getManager();
	}
}
