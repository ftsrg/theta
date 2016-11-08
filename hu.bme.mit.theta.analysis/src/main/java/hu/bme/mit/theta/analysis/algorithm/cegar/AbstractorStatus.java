package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.common.ObjectUtils;

public final class AbstractorStatus {

	private final boolean safe;

	private AbstractorStatus(final boolean safe) {
		this.safe = safe;
	}

	public static AbstractorStatus create(final ARG<?, ?> arg) {
		return new AbstractorStatus(arg.isSafe());
	}

	public static AbstractorStatus safe() {
		return new AbstractorStatus(true);
	}

	public static AbstractorStatus unsafe() {
		return new AbstractorStatus(false);
	}

	public boolean isSafe() {
		return safe;
	}

	public boolean isUnsafe() {
		return !isSafe();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add("Safe: " + isSafe()).toString();
	}
}
