package hu.bme.mit.theta.analysis.automaton;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class AutomatonActionFunction<A extends AutomatonAction<L, E>, L extends Loc<L, E>, E extends Edge<L, E>>
		implements ActionFunction<AutomatonState<?, L, E>, A> {

	public final Function<? super E, ? extends A> actionCreator;

	private AutomatonActionFunction(final Function<? super E, ? extends A> actionCreator) {
		this.actionCreator = checkNotNull(actionCreator);
	}

	public static <A extends AutomatonAction<L, E>, L extends Loc<L, E>, E extends Edge<L, E>> AutomatonActionFunction<A, L, E> create(
			final Function<? super E, ? extends A> actionCreator) {
		return new AutomatonActionFunction<>(actionCreator);
	}

	@Override
	public Collection<? extends A> getEnabledActionsFor(final AutomatonState<?, L, E> state) {
		final Collection<A> actions = new ArrayList<>();
		final L loc = state.getLoc();

		for (final E outEdge : loc.getOutEdges()) {
			final A action = actionCreator.apply(outEdge);
			actions.add(action);
		}

		return actions;
	}

}
