package hu.bme.mit.theta.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.formalism.ta.constr.UnitConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public abstract class AbstractUnitConstr implements UnitConstr {

	private final ClockDecl clock;
	private final int bound;

	private volatile int hashCode = 0;

	protected AbstractUnitConstr(final ClockDecl clock, final int bound) {
		this.clock = checkNotNull(clock);
		this.bound = bound;
	}

	@Override
	public final ClockDecl getClock() {
		return clock;
	}

	@Override
	public final int getBound() {
		return bound;
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return ImmutableSet.of(clock);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + clock.hashCode();
			result = 31 * result + bound;
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(clock.getName());
		sb.append(" ");
		sb.append(getOperatorLabel());
		sb.append(" ");
		sb.append(bound);
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
