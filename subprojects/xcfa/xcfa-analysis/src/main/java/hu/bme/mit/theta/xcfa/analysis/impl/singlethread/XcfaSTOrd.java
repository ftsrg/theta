package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaSTOrd<S extends ExprState> implements PartialOrd<XcfaSTState<S>> {

	private final PartialOrd<S> partialOrd;

	private XcfaSTOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState> XcfaSTOrd<S> create(final PartialOrd<S> partialOrd) {
		return new XcfaSTOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(final XcfaSTState<S> state1, final XcfaSTState<S> state2) {
		return 	state1.getCurrentLoc().equals(state2.getCurrentLoc()) &&
				partialOrd.isLeq(state1.getGlobalState(), state2.getGlobalState());
	}
}
