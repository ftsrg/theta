package hu.bme.mit.theta.analysis.tcfa;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

class TcfaActionFunction implements ActionFunction<TcfaState<?>, TcfaAction> {

	private static final TcfaActionFunction INSTANCE = new TcfaActionFunction();

	private TcfaActionFunction() {
	}

	static TcfaActionFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<TcfaAction> getEnabledActionsFor(final TcfaState<?> state) {
		final Collection<TcfaAction> tcfaActions = new ArrayList<>();
		final TcfaLoc loc = state.getLoc();

		for (final TcfaEdge outEdge : loc.getOutEdges()) {
			tcfaActions.add(new TcfaAction(outEdge));
		}

		return tcfaActions;
	}

}
