package hu.bme.mit.theta.analysis.cfa;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public final class CfaLts implements LTS<CfaState<?>, CfaAction> {

	private final Map<Loc, Collection<CfaAction>> actions;

	public CfaLts() {
		actions = new HashMap<>();
	}

	@Override
	public Collection<CfaAction> getEnabledActionsFor(final CfaState<?> state) {
		return actions.computeIfAbsent(state.getLoc(), loc -> {
			return loc.getOutEdges().stream().map(CfaAction::create).collect(Collectors.toList());
		});
	}

}
