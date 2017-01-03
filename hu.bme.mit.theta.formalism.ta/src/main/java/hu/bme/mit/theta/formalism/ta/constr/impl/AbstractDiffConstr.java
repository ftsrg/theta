package hu.bme.mit.theta.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.formalism.ta.constr.DiffConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public abstract class AbstractDiffConstr implements DiffConstr {

	private final ClockDecl leftClock;
	private final ClockDecl rightClock;
	private final int bound;

	private volatile int hashCode = 0;

	protected AbstractDiffConstr(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		this.leftClock = checkNotNull(leftClock);
		this.rightClock = checkNotNull(rightClock);
		this.bound = bound;
	}

	@Override
	public final ClockDecl getLeftClock() {
		return leftClock;
	}

	@Override
	public final ClockDecl getRightClock() {
		return rightClock;
	}

	@Override
	public final int getBound() {
		return bound;
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return ImmutableSet.of(leftClock, rightClock);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + leftClock.hashCode();
			result = 31 * result + rightClock.hashCode();
			result = 31 * result + bound;
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(leftClock.getName());
		sb.append(" - ");
		sb.append(rightClock.getName());
		sb.append(' ');
		sb.append(getOperatorLabel());
		sb.append(' ');
		sb.append(bound);
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
