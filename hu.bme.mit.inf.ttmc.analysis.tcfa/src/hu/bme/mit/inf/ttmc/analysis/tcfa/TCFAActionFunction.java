package hu.bme.mit.inf.ttmc.analysis.tcfa;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaLoc;

class TCFAActionFunction implements ActionFunction<TCFAState<?>, TCFAAction> {

	private static final TCFAActionFunction INSTANCE = new TCFAActionFunction();

	private TCFAActionFunction() {
	}

	static TCFAActionFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<TCFAAction> getEnabledActionsFor(final TCFAState<?> state) {
		final Collection<TCFAAction> tcfaActions = new ArrayList<>();
		final TcfaLoc loc = state.getLoc();

		for (final TcfaEdge outEdge : loc.getOutEdges()) {
			tcfaActions.add(new TCFAAction(outEdge));
		}

		return tcfaActions;
	}

}
