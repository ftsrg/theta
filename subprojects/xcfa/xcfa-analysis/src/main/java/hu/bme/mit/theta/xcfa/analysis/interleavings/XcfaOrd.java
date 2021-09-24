package hu.bme.mit.theta.xcfa.analysis.interleavings;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.List;
import java.util.stream.Collectors;

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
		if(state1.getEnabledProcesses().size() != state2.getEnabledProcesses().size()) return false;
		final List<XcfaLocation> locs1 = state1.getEnabledProcesses().stream().map(integer -> state1.getProcessLocs().get(integer)).collect(Collectors.toList());
		final List<XcfaLocation> locs2 = state2.getEnabledProcesses().stream().map(integer -> state2.getProcessLocs().get(integer)).collect(Collectors.toList());

		return locs1.containsAll(locs2) && locs2.containsAll(locs1) && state1.isLeq(partialOrd, state2);
	}
}
