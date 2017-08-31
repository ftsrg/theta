package hu.bme.mit.theta.analysis.cfa;

import java.util.Collection;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.loc.LocLts;
import hu.bme.mit.theta.analysis.loc.LocState;

public final class CfaLts implements LTS<LocState<?>, CfaAction> {

	private static final CfaLts INSTANCE = new CfaLts();

	private final LocLts lts;

	private CfaLts() {
		lts = LocLts.create(CfaAction::create);
	}

	public static CfaLts getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<CfaAction> getEnabledActionsFor(final LocState<?> state) {
		return lts.getEnabledActionsFor(state).stream().map(a -> (CfaAction) a).collect(Collectors.toList());
	}

}
