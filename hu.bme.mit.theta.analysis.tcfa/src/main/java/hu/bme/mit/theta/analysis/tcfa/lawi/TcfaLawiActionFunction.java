package hu.bme.mit.theta.analysis.tcfa.lawi;

import java.util.Collection;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaActionFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;

final class TcfaLawiActionFunction implements ActionFunction<TcfaLawiState, TcfaAction> {

	private static final TcfaLawiActionFunction INSTANCE = new TcfaLawiActionFunction();

	private final ActionFunction<TcfaState<?>, TcfaAction> actionFunction;

	private TcfaLawiActionFunction() {
		actionFunction = TcfaActionFunction.getInstance();
	}

	public static TcfaLawiActionFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<? extends TcfaAction> getEnabledActionsFor(final TcfaLawiState state) {
		return actionFunction.getEnabledActionsFor(state.getState());
	}

}
