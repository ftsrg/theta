package hu.bme.mit.theta.xcfa.analysis.interleavings.dpor;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.interleavings.allinterleavings.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public final class DporXcfaLts implements LTS<XcfaState<?>, XcfaAction> {
	private static int counter = 0;
	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?> state) {
		final Collection<XcfaAction> globalXcfaActions = new ArrayList<>();
		final List<XcfaAction> localXcfaActions = new ArrayList<>();
		for (Integer enabledProcess : state.getEnabledProcesses()) {
			final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
				for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
					final XcfaAction xcfaAction = XcfaAction.create(enabledProcess, outgoingEdge);
					if(outgoingEdge.getLabels().stream().anyMatch(label -> label instanceof XcfaLabel.FenceXcfaLabel || LabelUtils.getVars(label).stream().anyMatch(loc.getParent().getParent().getParent().getGlobalVars()::contains))) {
						globalXcfaActions.add(xcfaAction);
					} else {
						localXcfaActions.add(xcfaAction);
					}
				}
		}
		if(localXcfaActions.size() != 0) return List.of(localXcfaActions.get(counter++ % localXcfaActions.size()));
		else return globalXcfaActions;
	}

}
