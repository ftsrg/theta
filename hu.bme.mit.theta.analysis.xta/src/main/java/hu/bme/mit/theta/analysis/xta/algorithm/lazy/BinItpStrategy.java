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

public final class BinItpStrategy extends ItpStrategy {

	private BinItpStrategy(final XtaSystem system, final ItpOperator operator) {
		super(system, operator);
	}

	public static BinItpStrategy create(final XtaSystem system, final ItpOperator operator) {
		return new BinItpStrategy(system, operator);
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

	private void blockZone(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState zone,
			final Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> uncoveredNodes, final Builder statistics) {
		final ZoneState abstractZone = node.getState().getState().getInterpolant();
		if (abstractZone.isConsistentWith(zone)) {

			statistics.refine();

			final ZoneState concreteZone = node.getState().getState().getZone();

			statistics.startInterpolation();
			final ZoneState interpolant = interpolate(concreteZone, zone);
			statistics.stopInterpolation();

			strengthen(node, interpolant);
			maintainCoverage(node, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<ItpZoneState>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<ItpZoneState>, XtaAction> parent = inEdge.getSource();
				final Collection<ZoneState> badZones = interpolant.complement();
				for (final ZoneState badZone : badZones) {
					final ZoneState preBadZone = pre(badZone, action);
					blockZone(parent, preBadZone, uncoveredNodes, statistics);
				}
			}
		}
	}

}
