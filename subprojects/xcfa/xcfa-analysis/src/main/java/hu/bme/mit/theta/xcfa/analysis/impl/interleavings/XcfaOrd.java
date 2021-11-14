package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.LinkedHashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaOrd<S extends ExprState> implements PartialOrd<hu.bme.mit.theta.xcfa.analysis.common.XcfaState<S>> {

	private final PartialOrd<S> partialOrd;

	private XcfaOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState> XcfaOrd<S> create(final PartialOrd<S> partialOrd) {
		return new XcfaOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(final hu.bme.mit.theta.xcfa.analysis.common.XcfaState<S> cState1, final hu.bme.mit.theta.xcfa.analysis.common.XcfaState<S> cState2) {
		XcfaState<S> state1 = (XcfaState<S>) cState1;
		XcfaState<S> state2 = (XcfaState<S>) cState2;
		if(state1.getEnabledProcesses().size() != state2.getEnabledProcesses().size()) return false;
		Map<XcfaLocation, Integer> occurrences = new LinkedHashMap<>();
		for (XcfaLocation value : state1.getProcessLocs().values()) {
			occurrences.put(value, occurrences.getOrDefault(value, 0) + 1);
		}
		for (XcfaLocation value : state2.getProcessLocs().values()) {
			occurrences.put(value, occurrences.getOrDefault(value, 0) - 1);
		}
		return  occurrences.values().stream().allMatch(integer -> integer == 0) &&
				state1.isLeq(partialOrd, state2);
	}
}
