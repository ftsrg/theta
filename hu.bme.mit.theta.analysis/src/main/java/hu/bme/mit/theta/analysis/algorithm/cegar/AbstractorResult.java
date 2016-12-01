package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.common.ObjectUtils;

public final class AbstractorResult {

	private final boolean safe;

	private AbstractorResult(final boolean safe) {
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
