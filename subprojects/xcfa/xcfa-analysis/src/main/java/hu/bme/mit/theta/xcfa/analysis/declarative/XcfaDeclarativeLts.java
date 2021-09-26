package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;

public final class XcfaDeclarativeLts implements LTS<XcfaDeclarativeState<?>, XcfaDeclarativeAction> {
	@Override
	public Collection<XcfaDeclarativeAction> getEnabledActionsFor(final XcfaDeclarativeState<?> state) {
		final Collection<XcfaDeclarativeAction> xcfaActions = new ArrayList<>();
		final XcfaLocation loc = state.getCurrentLoc();
		for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
			final XcfaDeclarativeAction xcfaAction = XcfaDeclarativeAction.create(outgoingEdge);
			xcfaActions.add(xcfaAction);
		}
		if(xcfaActions.size() == 0 && state.getCurrentLoc().isErrorLoc()) {
			final Optional<Map.Entry<Integer, XcfaProcess>> backlogEntryOpt = state.getBacklog().entrySet().stream().findAny();
			if(backlogEntryOpt.isPresent()) {
				final XcfaLocation initLoc = backlogEntryOpt.get().getValue().getMainProcedure().getInitLoc();
				final XcfaDeclarativeAction xcfaAction = XcfaDeclarativeAction.createThreadChange(backlogEntryOpt.get().getKey(), XcfaEdge.of(state.getCurrentLoc(), initLoc, List.of()));
				xcfaActions.add(xcfaAction);
			}
		}
		return xcfaActions;
	}

}
