package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

public final class XcfaLts implements LTS<XcfaState<?>, XcfaAction> {
	private int roundRobinCnt = 0;
	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?> state) {
		final List<List<XcfaAction>> xcfaActions = new ArrayList<>();
		final Set<Integer> globalActions = new LinkedHashSet<>();
		for (Integer enabledProcess : state.getEnabledProcesses()) {
			final List<XcfaAction> processActions = new ArrayList<>();
			final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
			for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
				final XcfaAction xcfaAction = XcfaAction.create(enabledProcess, outgoingEdge);
//				if(xcfaAction.getLabels().stream().anyMatch(label -> LabelUtils.isGlobal(label, outgoingEdge.getSource().getParent().getParent().getParent()))) {
//					globalActions.add(xcfaActions.size());
//				}
				processActions.add(xcfaAction);
			}
			xcfaActions.add(processActions);
		}
//		if(globalActions.size() == 0) {
//			return xcfaActions.get(roundRobinCnt++ % xcfaActions.size());
//		} else {
			final List<XcfaAction> ret = new ArrayList<>();
			for (List<XcfaAction> xcfaAction : xcfaActions) {
				ret.addAll(xcfaAction);
			}
//			for (Integer globalAction : globalActions) {
//				ret.addAll(xcfaActions.get(globalAction));
//			}
			return ret;
//		}
	}

}
