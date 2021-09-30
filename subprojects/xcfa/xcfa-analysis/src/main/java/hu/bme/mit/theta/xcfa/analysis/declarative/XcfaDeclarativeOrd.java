package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclarativeOrd<S extends ExprState> implements PartialOrd<XcfaDeclarativeState<S>> {

	private final PartialOrd<S> partialOrd;

	private XcfaDeclarativeOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState> XcfaDeclarativeOrd<S> create(final PartialOrd<S> partialOrd) {
		return new XcfaDeclarativeOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(final XcfaDeclarativeState<S> state1, final XcfaDeclarativeState<S> state2) {
		return 	state1.getCurrentLoc().equals(state2.getCurrentLoc()) &&
				state1.getBacklog().size() == state2.getBacklog().size() &&
				state1.getBacklog().keySet().equals(state2.getBacklog().keySet()) &&
				partialOrd.isLeq(state1.getGlobalState(), state2.getGlobalState()) &&
				state1.getStores().equals(state2.getStores()) &&
				state1.getLoads().equals(state2.getLoads());
	}
}
