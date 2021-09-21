package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaOrd<S extends ExprState> implements PartialOrd<XcfaState<S>> {

	private final PartialOrd<S> partialOrd;

	private XcfaOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState> XcfaOrd<S> create(final PartialOrd<S> partialOrd) {
		return new XcfaOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(final XcfaState<S> state1, final XcfaState<S> state2) {
		return state1.getEnabledProcesses().equals(state2.getEnabledProcesses()) && partialOrd.isLeq(state1.getGlobalState(), state2.getGlobalState());
	}
}
