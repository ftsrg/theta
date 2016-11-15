package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class LocActionFunction<A extends LocAction<L, E>, L extends Loc<L, E>, E extends Edge<L, E>>
		implements LTS<LocState<?, L, E>, A> {

	public final Function<? super E, ? extends A> actionCreator;

	private LocActionFunction(final Function<? super E, ? extends A> actionCreator) {
		this.actionCreator = checkNotNull(actionCreator);
	}

	public static <A extends LocAction<L, E>, L extends Loc<L, E>, E extends Edge<L, E>> LocActionFunction<A, L, E> create(
			final Function<? super E, ? extends A> actionCreator) {
		return new LocActionFunction<>(actionCreator);
	}

	@Override
	public Collection<A> getEnabledActionsFor(final LocState<?, L, E> state) {
		final Collection<A> actions = new ArrayList<>();
		final L loc = state.getLoc();

		for (final E outEdge : loc.getOutEdges()) {
			final A action = actionCreator.apply(outEdge);
			actions.add(action);
		}

		return actions;
	}

}
