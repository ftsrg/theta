package hu.bme.mit.theta.formalism.ta.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.TaEdge;
import hu.bme.mit.theta.formalism.ta.TaLoc;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;

final class MutableTaEdge implements TaEdge {

	private final TaLoc source;
	private final TaLoc target;
	private final ClockConstr guard;
	private final Collection<? extends ClockDecl> resets;

	public MutableTaEdge(final TaLoc source, final ClockConstr guard, final Collection<? extends ClockDecl> resets,
			final TaLoc target) {
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
	public TaLoc getSource() {
		return source;
	}

	@Override
	public TaLoc getTarget() {
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
