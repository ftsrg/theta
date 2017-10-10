package hu.bme.mit.theta.formalism.cfa.analysis.lts;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaAction;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaState;

/**
 * A caching layer over CFA LTS implementations. It only computes actions for
 * each location once and stores the result for later queries.
 */
public final class CfaCachedLts implements CfaLts {

	private final CfaLts lts;
	private final Map<Loc, Collection<CfaAction>> actionCache;

	public CfaCachedLts(final CfaLts lts) {
		this.lts = lts;
		this.actionCache = new HashMap<>();
	}

	@Override
	public Collection<CfaAction> getEnabledActionsFor(final CfaState<?> state) {
		final Loc loc = state.getLoc();
		if (!actionCache.containsKey(loc)) {
			actionCache.put(loc, lts.getEnabledActionsFor(state));
		}
		return actionCache.get(loc);
	}

}
