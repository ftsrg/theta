package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsOrd<S extends ExprState> implements PartialOrd<XstsState<S>> {

	private final PartialOrd<S> partialOrd;

	private XstsOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState> XstsOrd<S> create(final PartialOrd<S> partialOrd) {
		return new XstsOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(XstsState<S> state1, XstsState<S> state2) {
		return state1.lastActionWasEnv() == state2.lastActionWasEnv()
				&& state1.isInitialized() == state2.isInitialized()
				&& partialOrd.isLeq(state1.getState(), state2.getState());
	}
}
