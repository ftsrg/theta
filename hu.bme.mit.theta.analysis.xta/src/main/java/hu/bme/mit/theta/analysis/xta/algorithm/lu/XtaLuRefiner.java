package hu.bme.mit.theta.analysis.xta.algorithm.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.algorithm.itp.XtaItpStatistics;
import hu.bme.mit.theta.analysis.zone.BoundFunction;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneState;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaLuRefiner {

	private final Waitlist<ArgNode<XtaState<LuZoneState>, XtaAction>> waitlist;
	private final XtaItpStatistics.Builder statisticsBuilder;

	private XtaLuRefiner(final XtaSystem system, final Waitlist<ArgNode<XtaState<LuZoneState>, XtaAction>> waitlist,
			final XtaItpStatistics.Builder statisticsBuilder) {
		checkNotNull(system);
		this.waitlist = checkNotNull(waitlist);
		this.statisticsBuilder = checkNotNull(statisticsBuilder);
	}

	public static XtaLuRefiner create(final XtaSystem system,
			final Waitlist<ArgNode<XtaState<LuZoneState>, XtaAction>> waitlist,
			final XtaItpStatistics.Builder statisticsBuilder) {
		return new XtaLuRefiner(system, waitlist, statisticsBuilder);
	}

	public void refine(final ArgNode<XtaState<LuZoneState>, XtaAction> node, final BoundFunction boundFunction) {
		statisticsBuilder.startRefinement();
		propagateBounds(node, boundFunction, false);
		statisticsBuilder.stopRefinement();
	}

	public void refine(final ArgNode<XtaState<LuZoneState>, XtaAction> node) {
		statisticsBuilder.startRefinement();
		propagateBounds(node, BoundFunction.top(), true);
		statisticsBuilder.stopRefinement();
	}

	private void propagateBounds(final ArgNode<XtaState<LuZoneState>, XtaAction> node,
			final BoundFunction boundFunction, final boolean forcePropagate) {

		final BoundFunction oldBoundFunction = node.getState().getState().getBoundFunction();

		if (forcePropagate || !boundFunction.isLeq(oldBoundFunction)) {
			statisticsBuilder.refine();

			refineNode(node, boundFunction);
			maintainCoverage(node);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<LuZoneState>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<LuZoneState>, XtaAction> parent = inEdge.getSource();
				final BoundFunction preBound = XtaLuZoneUtils.pre(boundFunction, action);
				propagateBounds(parent, preBound, false);
			}
		}
	}

	private void refineNode(final ArgNode<XtaState<LuZoneState>, XtaAction> node, final BoundFunction boundFunction) {
		final BoundFunction oldBoundFunction = node.getState().getState().getBoundFunction();
		final BoundFunction newBoundFunction = oldBoundFunction.merge(boundFunction);
		final LuZoneState newItpState = node.getState().getState().withBoundFunction(newBoundFunction);
		node.setState(node.getState().withState(newItpState));
	}

	private void maintainCoverage(final ArgNode<XtaState<LuZoneState>, XtaAction> node) {
		waitlist.addAll(node.getCoveredNodes());
		node.clearCoveredNodes();
	}

}
