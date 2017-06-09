package hu.bme.mit.theta.analysis.cfa;

import java.util.Collection;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.loc.LocLts;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

public final class CfaLts implements LTS<LocState<?, CfaLoc, CfaEdge>, CfaAction> {

	private static final CfaLts INSTANCE = new CfaLts();

	private final LocLts<CfaAction, CfaLoc, CfaEdge> lts;

	private CfaLts() {
		lts = LocLts.create(CfaAction::create);
	}

	public static CfaLts getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<CfaAction> getEnabledActionsFor(final LocState<?, CfaLoc, CfaEdge> state) {
		return lts.getEnabledActionsFor(state);
	}

}
