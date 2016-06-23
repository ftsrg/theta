package hu.bme.mit.inf.ttmc.analysis.tcfa;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.AnalysisContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAAnalysisContext implements AnalysisContext<TCFAState<?>, TCFAAction> {

	@Override
	public Collection<TCFAAction> getEnabledActionsFor(final TCFAState<?> state) {
		final Collection<TCFAAction> tcfaAction = new ArrayList<>();
		final TCFALoc loc = state.getLoc();

		for (final TCFAEdge outEdge : loc.getOutEdges()) {
			tcfaAction.add(TCFAAction.discrete(outEdge));
		}

		if (!loc.isUrgent()) {
			tcfaAction.add(TCFAAction.delay(loc));
		}

		return tcfaAction;
	}

}
