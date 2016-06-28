package hu.bme.mit.inf.ttmc.formalism.ta.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.TAEdge;
import hu.bme.mit.inf.ttmc.formalism.ta.TALoc;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;

final class MutableTAEdge implements TAEdge {

	private final TALoc source;
	private final TALoc target;
	private final ClockConstr guard;
	private final Collection<? extends ClockDecl> resets;

	public MutableTAEdge(final TALoc source, final ClockConstr guard, final Collection<? extends ClockDecl> resets,
			final TALoc target) {
		checkNotNull(source);
		checkNotNull(guard);
		checkNotNull(resets);
		checkNotNull(target);

		this.source = source;
		this.guard = guard;
		this.resets = ImmutableSet.copyOf(resets);
		this.target = target;

	}

	@Override
	public TALoc getSource() {
		return source;
	}

	@Override
	public TALoc getTarget() {
		return target;
	}

	@Override
	public ClockConstr getGuard() {
		return guard;
	}

	@Override
	public Collection<? extends ClockDecl> getResets() {
		return resets;
	}

}
