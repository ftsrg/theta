package hu.bme.mit.inf.ttmc.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Stream;

import hu.bme.mit.inf.ttmc.analysis.AutomatonAbstraction;
import hu.bme.mit.inf.ttmc.analysis.impl.NullPrecision;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Automaton;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Edge;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Loc;

public abstract class LocAbstraction<L extends Loc<L, E>, E extends Edge<L, E>> implements AutomatonAbstraction<LocState<L>, NullPrecision, E> {

	private final Automaton<L, ?> automaton;

	protected LocAbstraction(final Automaton<L, ?> automaton) {
		this.automaton = automaton;
	}

	@Override
	public Collection<? extends LocState<L>> getStartStates(final NullPrecision precision) {
		return Collections.singleton(LocState.create(automaton.getInitLoc()));
	}

	@Override
	public Collection<? extends LocState<L>> getSuccStates(final LocState<L> state, final NullPrecision precision) {
		checkNotNull(state);

		final L loc = state.getLoc();
		final Stream<L> succLocs = loc.getOutEdges().stream().map(e -> e.getTarget());
		final Collection<LocState<L>> succStates = succLocs.map(l -> LocState.create(l)).collect(toList());
		return succStates;
	}

	@Override
	public Collection<? extends LocState<L>> getSuccStatesForEdge(final LocState<L> state, final NullPrecision precision, final E edge) {
		checkNotNull(state);
		checkNotNull(edge);

		final L loc = state.getLoc();
		if (loc.getOutEdges().contains(edge)) {
			final LocState<L> succState = LocState.create(edge.getTarget());
			return Collections.singletonList(succState);
		} else {
			return Collections.emptyList();
		}
	}

}
