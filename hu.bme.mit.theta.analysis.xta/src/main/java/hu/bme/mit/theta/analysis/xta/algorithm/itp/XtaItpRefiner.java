package hu.bme.mit.theta.analysis.xta.algorithm.itp;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.xta.zone.XtaZoneUtils.pre;

import java.util.Collection;

import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaItpRefiner {

	private final ZonePrec prec;
	private final Waitlist<ArgNode<XtaState<ItpZoneState>, XtaAction>> waitlist;
	private final XtaItpStatistics.Builder statisticsBuilder;

	private XtaItpRefiner(final XtaSystem system, final Waitlist<ArgNode<XtaState<ItpZoneState>, XtaAction>> waitlist,
			final XtaItpStatistics.Builder statisticsBuilder) {
		checkNotNull(system);
		this.waitlist = checkNotNull(waitlist);
		this.statisticsBuilder = checkNotNull(statisticsBuilder);
		prec = ZonePrec.of(system.getClocks());
	}

	public static XtaItpRefiner create(final XtaSystem system,
			final Waitlist<ArgNode<XtaState<ItpZoneState>, XtaAction>> waitlist,
			final XtaItpStatistics.Builder statisticsBuilder) {
		return new XtaItpRefiner(system, waitlist, statisticsBuilder);
	}

	public void enforceZone(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState zone) {
		statisticsBuilder.startRefinement();
		final Collection<ZoneState> complementZones = zone.complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(node, complementZone);
		}
		statisticsBuilder.stopRefinement();
	}

	private void blockZone(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState zone) {
		final ZoneState abstractZone = node.getState().getState().getInterpolant();
		if (abstractZone.isConsistentWith(zone)) {

			statisticsBuilder.refine();

			final ZoneState concreteZone = node.getState().getState().getZone();

			statisticsBuilder.startInterpolation();
			final ZoneState interpolant = ZoneState.interpolant(concreteZone, zone);
			statisticsBuilder.stopInterpolation();

			refine(node, interpolant);
			maintainCoverage(node, interpolant);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<ItpZoneState>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<ItpZoneState>, XtaAction> parent = inEdge.getSource();
				final Collection<ZoneState> badZones = interpolant.complement();
				for (final ZoneState badZone : badZones) {
					final ZoneState preBadZone = pre(badZone, action, prec);
					blockZone(parent, preBadZone);
				}
			}
		}
	}

	private void refine(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState interpolant) {
		final ZoneState oldAbstractZone = node.getState().getState().getInterpolant();
		final ZoneState newAbstractZone = ZoneState.intersection(oldAbstractZone, interpolant);
		final ItpZoneState newItpState = node.getState().getState().withInterpolant(newAbstractZone);
		node.setState(node.getState().withState(newItpState));
	}

	private void maintainCoverage(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState interpolant) {
		waitlist.addAll(node.getCoveredNodes());
		node.clearCoveredNodes();
	}

}
