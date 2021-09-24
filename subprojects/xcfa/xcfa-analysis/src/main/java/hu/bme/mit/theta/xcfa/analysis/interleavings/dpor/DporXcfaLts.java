package hu.bme.mit.theta.xcfa.analysis.interleavings.dpor;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.interleavings.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.ArrayList;
import java.util.Collection;

public final class DporXcfaLts implements LTS<XcfaState<?>, XcfaAction> {
	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?> state) {

		final XcfaAction lastAction = state.getLastAction();
		if(lastAction != null && lastAction.getLabels().stream().allMatch(label -> LabelUtils.isGlobal(label, lastAction.getSource().getParent().getParent().getParent()))) {
			final XcfaLocation loc = state.getProcessLocs().get(lastAction.getProcess());
			final Collection<XcfaAction> xcfaActions = new ArrayList<>();
			boolean ok = true;
			for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
				final XcfaAction xcfaAction = XcfaAction.create(lastAction.getProcess(), outgoingEdge);
				if(outgoingEdge.getLabels().stream().noneMatch(label -> LabelUtils.isGlobal(label, lastAction.getSource().getParent().getParent().getParent()))) {
					xcfaActions.add(xcfaAction);
				} else {
					ok = false;
					break;
				}
			}
			if(ok) return xcfaActions;
		}

		final Collection<XcfaAction> xcfaActions = new ArrayList<>();
		for (Integer enabledProcess : state.getEnabledProcesses()) {
			final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
			for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
				final XcfaAction xcfaAction = XcfaAction.create(enabledProcess, outgoingEdge);
				xcfaActions.add(xcfaAction);
			}
		}
		return xcfaActions;
	}

}
