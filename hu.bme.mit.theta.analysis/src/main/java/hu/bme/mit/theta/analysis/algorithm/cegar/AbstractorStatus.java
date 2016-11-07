package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.common.ObjectUtils;

public final class AbstractorStatus<S extends State, A extends Action, P extends Precision> {
	private final AbstractionState<S, A, P> abstractionState;

	private AbstractorStatus(final AbstractionState<S, A, P> abstractionState) {
		this.abstractionState = checkNotNull(abstractionState);
	}

	public static <S extends State, A extends Action, P extends Precision> AbstractorStatus<S, A, P> create(
			final AbstractionState<S, A, P> abstractionState) {
		return new AbstractorStatus<>(abstractionState);
	}

	public AbstractionState<S, A, P> getAbstractionState() {
		return abstractionState;
	}

	public ARG<S, A> getArg() {
		return abstractionState.getArg();
	}

	public boolean isSafe() {
		return getArg().isSafe();
	}

	public boolean isUnsafe() {
		return !isSafe();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add("Safe: " + isSafe()).toString();
	}
}
