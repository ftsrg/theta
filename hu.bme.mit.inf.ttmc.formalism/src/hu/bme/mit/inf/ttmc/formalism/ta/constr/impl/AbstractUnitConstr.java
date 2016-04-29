package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitConstr;

public abstract class AbstractUnitConstr implements UnitConstr {

	private final Clock clock;
	private final int bound;

	private volatile int hashCode = 0;

	protected AbstractUnitConstr(final Clock clock, final int bound) {
		this.clock = checkNotNull(clock);
		this.bound = bound;
	}

	@Override
	public final Clock getClock() {
		return clock;
	}

	@Override
	public final int getBound() {
		return bound;
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
		sb.append("CC");
		sb.append("(");
		sb.append(clock.getName());
		sb.append(" ");
		sb.append(getOperatorLabel());
		sb.append(" ");
		sb.append(bound);
		sb.append(")");
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
