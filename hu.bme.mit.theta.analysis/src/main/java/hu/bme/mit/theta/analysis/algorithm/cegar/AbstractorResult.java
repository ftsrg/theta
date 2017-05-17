package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.common.ObjectUtils;

/**
 * Represents the result of the Abstractor component, that can be either safe or
 * unsafe.
 */
public final class AbstractorResult {

	private final boolean safe;

	public AbstractorResult(final boolean safe) {
		this.safe = safe;
	}

	public static AbstractorResult safe() {
		return new AbstractorResult(true);
	}

	public static AbstractorResult unsafe() {
		return new AbstractorResult(false);
	}

	public boolean isSafe() {
		return safe;
	}

	public boolean isUnsafe() {
		return !isSafe();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(isSafe() ? "Safe" : "Unsafe").toString();
	}
}
