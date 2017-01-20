package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaLts;
import hu.bme.mit.theta.formalism.tcfa.TCFA;

final class TcfaLawiLts implements LTS<TcfaLawiState, TcfaAction> {

	private final TcfaLts lts;

	private TcfaLawiLts(final TCFA tcfa) {
		checkNotNull(tcfa);
		lts = TcfaLts.create(tcfa);
	}

	public static TcfaLawiLts create(final TCFA tcfa) {
		return new TcfaLawiLts(tcfa);
	}

	@Override
	public Collection<TcfaAction> getEnabledActionsFor(final TcfaLawiState state) {
		return lts.getEnabledActionsFor(state.getState());
	}

}
