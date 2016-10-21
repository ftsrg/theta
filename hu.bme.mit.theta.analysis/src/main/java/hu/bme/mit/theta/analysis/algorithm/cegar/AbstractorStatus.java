package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public final class AbstractorStatus<S extends State, A extends Action> {
	private final ARG<S, A> arg;

	private AbstractorStatus(final ARG<S, A> arg) {
		this.arg = arg;
	}

	public static <S extends State, A extends Action> AbstractorStatus<S, A> create(final ARG<S, A> arg) {
		return new AbstractorStatus<>(arg);
	}

	public ARG<S, A> getArg() {
		return arg;
	}

	public boolean isSafe() {
		return arg.getTargetNodes().size() == 0;
	}

	public boolean isUnsafe() {
		return !isSafe();
	}

}
