package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.loc.LocLts;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaLts implements LTS<LocState<?, TcfaLoc, TcfaEdge>, TcfaAction> {

	private final LTS<LocState<?, TcfaLoc, TcfaEdge>, TcfaAction> lts;

	private TcfaLts(final TCFA tcfa) {
		checkNotNull(tcfa);
		lts = LocLts.create(edge -> TcfaAction.create(tcfa, edge));
	}

	public static TcfaLts create(final TCFA tcfa) {
		return new TcfaLts(tcfa);
	}

	@Override
	public Collection<TcfaAction> getEnabledActionsFor(final LocState<?, TcfaLoc, TcfaEdge> state) {
		return lts.getEnabledActionsFor(state);
	}

}
