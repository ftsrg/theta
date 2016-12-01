package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class LocLts<A extends LocAction<L, E>, L extends Loc<L, E>, E extends Edge<L, E>>
		implements LTS<LocState<?, L, E>, A> {

	private final Function<? super E, ? extends A> actionFactory;
	private final Map<L, Collection<A>> actions;

	private LocLts(final Function<? super E, ? extends A> actionFactory) {
		this.actionFactory = checkNotNull(actionFactory);
		actions = new HashMap<>();
	}

	public static <A extends LocAction<L, E>, L extends Loc<L, E>, E extends Edge<L, E>> LocLts<A, L, E> create(
			final Function<? super E, ? extends A> actionCreator) {
		return new LocLts<>(actionCreator);
	}

	@Override
	public Collection<A> getEnabledActionsFor(final LocState<?, L, E> state) {
		return actions.computeIfAbsent(state.getLoc(), loc -> {
			return loc.getOutEdges().stream().map(e -> actionFactory.apply(e)).collect(toList());
		});
	}

}
