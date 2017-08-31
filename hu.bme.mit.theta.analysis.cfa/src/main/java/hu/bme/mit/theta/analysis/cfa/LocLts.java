package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public final class LocLts implements LTS<LocState<?>, LocAction> {

	private final Function<Edge, LocAction> actionFactory;
	private final Map<Loc, Collection<LocAction>> actions;

	private LocLts(final Function<Edge, LocAction> actionFactory) {
		this.actionFactory = checkNotNull(actionFactory);
		actions = new HashMap<>();
	}

	public static LocLts create(final Function<Edge, LocAction> actionCreator) {
		return new LocLts(actionCreator);
	}

	@Override
	public Collection<LocAction> getEnabledActionsFor(final LocState<?> state) {
		return actions.computeIfAbsent(state.getLoc(), loc -> {
			return loc.getOutEdges().stream().map(e -> actionFactory.apply(e)).collect(Collectors.toList());
		});
	}

}
