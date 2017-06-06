package hu.bme.mit.theta.splittingcegar.common.data;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.sts.STS;

/**
 * Base class for abstract systems.
 */
public abstract class AbstractSystemBase implements AbstractSystem {
	protected STS sts;
	protected Set<VarDecl<? extends Type>> vars;

	public AbstractSystemBase(final STS sts) {
		this.sts = checkNotNull(sts);
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
}
