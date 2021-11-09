package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;

public final class XcfaSTLts implements LTS<XcfaSTState<?>, XcfaSTAction> {
	@Override
	public Collection<XcfaSTAction> getEnabledActionsFor(final XcfaSTState<?> state) {
		final Collection<XcfaSTAction> xcfaActions = new ArrayList<>();
		final XcfaLocation loc = state.getCurrentLoc();
		for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
			final XcfaSTAction xcfaAction = XcfaSTAction.create(outgoingEdge);
			xcfaActions.add(xcfaAction);
		}
		return xcfaActions;
	}

}
