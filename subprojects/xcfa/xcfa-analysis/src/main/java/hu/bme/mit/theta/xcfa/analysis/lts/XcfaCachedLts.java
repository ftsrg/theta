package hu.bme.mit.theta.xcfa.analysis.lts;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Collection;
import java.util.Map;

/**
 * A caching layer over CFA LTS implementations. It only computes actions for
 * each location once and stores the result for later queries.
 */
public final class XcfaCachedLts implements XcfaLts {

	private final XcfaLts lts;
	private final Map<Map<Integer, XcfaLocation>, Collection<XcfaAction>> actionCache;

	public XcfaCachedLts(final XcfaLts lts) {
		this.lts = lts;
		this.actionCache = Containers.createMap();
	}

	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?, ?, ?> state) {
		final Map<Integer, XcfaLocation> loc = state.getLocations();
		if (!actionCache.containsKey(loc)) {
			actionCache.put(loc, lts.getEnabledActionsFor(state));
		}
		return actionCache.get(loc);
	}

}
