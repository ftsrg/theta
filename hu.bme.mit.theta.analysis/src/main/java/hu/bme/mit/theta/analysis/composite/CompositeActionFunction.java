package hu.bme.mit.theta.analysis.composite;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import com.google.common.collect.Sets;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.State;

public class CompositeActionFunction<S1 extends State, S2 extends State, A extends Action>
		implements ActionFunction<CompositeState<? extends S1, ? extends S2>, A> {

	private final ActionFunction<? super S1, ? extends A> actionFunction1;
	private final ActionFunction<? super S2, ? extends A> actionFunction2;

	public CompositeActionFunction(final ActionFunction<? super S1, ? extends A> actionFunction1,
			final ActionFunction<? super S2, ? extends A> actionFunction2) {
		this.actionFunction1 = checkNotNull(actionFunction1);
		this.actionFunction2 = checkNotNull(actionFunction2);
	}

	@Override
	public Collection<A> getEnabledActionsFor(final CompositeState<? extends S1, ? extends S2> state) {
		final Set<A> actions1 = new HashSet<>(actionFunction1.getEnabledActionsFor(state._1()));
		final Set<A> actions2 = new HashSet<>(actionFunction2.getEnabledActionsFor(state._2()));
		return Sets.intersection(actions1, actions2);
	}

}
