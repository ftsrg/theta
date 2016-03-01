package hu.bme.mit.inf.ttmc.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;

public class LocTransferRelation implements TransferRelation<LocState> {

	@Override
	public Collection<LocState> getSuccessors(LocState state) {
		checkNotNull(state);
		
		final Collection<LocState> succStates = new ArrayList<>();
		
		final CFALoc loc = state.getLoc();
		for (CFAEdge outEdge : loc.getOutEdges()) {
			final CFALoc target = outEdge.getTarget();
			final LocState succState = new LocState(target);
			succStates.add(succState);
		}
		
		return succStates;
	}

	@Override
	public Collection<LocState> getSuccessors(LocState state, CFAEdge edge) {
		checkNotNull(state);
		checkNotNull(edge);
		
		final CFALoc loc = state.getLoc();
		final CFALoc source = edge.getSource();
		if (loc.equals(source)) {
			final CFALoc target = edge.getTarget();
			final LocState succState = new LocState(target);
			return Collections.singletonList(succState);
		}
		
		return Collections.emptyList();
	}

}
