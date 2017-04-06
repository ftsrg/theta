package hu.bme.mit.theta.analysis.xta.algorithm.lazy;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.algorithm.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class SeqItpStrategy extends ItpStrategy {

	private SeqItpStrategy(final XtaSystem system) {
		super(system);
	}

	public static SeqItpStrategy create(final XtaSystem system) {
		return new SeqItpStrategy(system);
	}

	@Override
	public Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> forceCover(
			final ArgNode<XtaState<ItpZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ItpZoneState>, XtaAction> coveringNode, final Builder statistics) {

		statistics.startRefinement();

		final Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> uncoveredNodes = new ArrayList<>();
		final Collection<ZoneState> complementZones = coveringNode.getState().getState().getInterpolant().complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(nodeToCover, complementZone, uncoveredNodes, statistics);
		}

		statistics.stopRefinement();
		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> refine(
			final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final Builder statistics) {

		statistics.startRefinement();

		final Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> uncoveredNodes = new ArrayList<>();
		blockZone(node, ZoneState.top(), uncoveredNodes, statistics);

		statistics.stopRefinement();
		return uncoveredNodes;
	}

	private ZoneState blockZone(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState zone,
			final Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> uncoveredNodes, final Builder statistics) {
		final ZoneState abstractZone = node.getState().getState().getInterpolant();
		if (abstractZone.isConsistentWith(zone)) {

			statistics.refine();

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<ItpZoneState>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<ItpZoneState>, XtaAction> parent = inEdge.getSource();

				final ZoneState B_pre = pre(zone, action);
				final ZoneState A_pre = blockZone(parent, B_pre, uncoveredNodes, statistics);

				final ZoneState B = zone;
				final ZoneState A = post(A_pre, action);

				statistics.startInterpolation();
				final ZoneState interpolant = ZoneState.interpolant(A, B);
				statistics.stopInterpolation();

				strengthen(node, interpolant);
				maintainCoverage(node, uncoveredNodes);

				return interpolant;
			} else {
				final ZoneState concreteZone = node.getState().getState().getZone();

				statistics.startInterpolation();
				final ZoneState interpolant = ZoneState.interpolant(concreteZone, zone);
				statistics.stopInterpolation();

				strengthen(node, interpolant);
				maintainCoverage(node, uncoveredNodes);

				return interpolant;
			}
		} else {
			return abstractZone;
		}
	}

}
