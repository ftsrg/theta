package hu.bme.mit.theta.xcfa.analysis.declarative.noota;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclOrd<S extends ExprState> implements PartialOrd<XcfaDeclState<S>> {

	private final PartialOrd<S> partialOrd;

	private XcfaDeclOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState> XcfaDeclOrd<S> create(final PartialOrd<S> partialOrd) {
		return new XcfaDeclOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(final XcfaDeclState<S> state1, final XcfaDeclState<S> state2) {
		return 	state1.getProcesses().equals(state2.getProcesses()) &&
				state1.getCurrentProcess().equals(state2.getCurrentProcess()) &&
				partialOrd.isLeq(state1.getState(), state2.getState()) &&
				state1.getStores().equals(state2.getStores()) &&
				state1.getRevisitableLoads().equals(state2.getRevisitableLoads());
	}
}
