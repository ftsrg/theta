package hu.bme.mit.inf.ttmc.formalism.ta.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.ta.TAEdge;
import hu.bme.mit.inf.ttmc.formalism.ta.TALoc;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Constr;

final class MutableTAEdge implements TAEdge {

	private final TALoc source;
	private final TALoc target;
	private final Constr guard;
	private final Collection<? extends Clock> resets;

	public MutableTAEdge(final TALoc source, final Constr guard, final Collection<? extends Clock> resets,
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
	public Constr getGuard() {
		return guard;
	}

	@Override
	public Collection<? extends Clock> getResets() {
		return resets;
	}

}
