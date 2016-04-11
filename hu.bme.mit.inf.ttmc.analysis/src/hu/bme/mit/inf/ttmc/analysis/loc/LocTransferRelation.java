package hu.bme.mit.inf.ttmc.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Stream;

import hu.bme.mit.inf.ttmc.analysis.AutomatonTransferRelation;
import hu.bme.mit.inf.ttmc.formalism.common.Edge;
import hu.bme.mit.inf.ttmc.formalism.common.Loc;

public class LocTransferRelation<L extends Loc<L, E>, E extends Edge<L, E>>
		implements AutomatonTransferRelation<LocState<L>, E> {

	@Override
	public Collection<LocState<L>> getSuccStates(final LocState<L> state) {
		checkNotNull(state);

		final L loc = state.getLoc();
		final Stream<L> succLocs = loc.getOutEdges().stream().map(e -> e.getTarget());
		final Collection<LocState<L>> succStates = succLocs.map(l -> LocState.create(l)).collect(toList());
		return succStates;
	}

	@Override
	public Collection<LocState<L>> getSuccStatesForEdge(final LocState<L> state, final E edge) {
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