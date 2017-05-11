package hu.bme.mit.theta.formalism.ta.constr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public abstract class UnitConstr extends AtomicConstr {

	private final ClockDecl clock;

	private volatile int hashCode = 0;

	protected UnitConstr(final ClockDecl clock, final int bound) {
		super(bound);
		this.clock = checkNotNull(clock);
	}

	public final ClockDecl getClock() {
		return clock;
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
			result = 31 * result + getBound();
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
		sb.append(getBound());
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
