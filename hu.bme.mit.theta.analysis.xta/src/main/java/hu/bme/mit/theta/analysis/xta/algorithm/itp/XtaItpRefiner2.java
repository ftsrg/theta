package hu.bme.mit.theta.analysis.xta.algorithm.itp;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.xta.zone.XtaZoneUtils.post;
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

public final class XtaItpRefiner2 {

	private final ZonePrec prec;
	private final Waitlist<ArgNode<XtaState<ItpZoneState>, XtaAction>> waitlist;

	private XtaItpRefiner2(final XtaSystem system, final Waitlist<ArgNode<XtaState<ItpZoneState>, XtaAction>> waitlist) {
		checkNotNull(system);
		this.waitlist = checkNotNull(waitlist);
		prec = ZonePrec.of(system.getClocks());
	}

	public static XtaItpRefiner2 create(final XtaSystem system,
			final Waitlist<ArgNode<XtaState<ItpZoneState>, XtaAction>> waitlist) {
		return new XtaItpRefiner2(system, waitlist);
	}

	public void enforceZone(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState zone) {
		final Collection<ZoneState> complementZones = zone.complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(node, complementZone);
		}
	}

	private ZoneState blockZone(final ArgNode<XtaState<ItpZoneState>, XtaAction> node, final ZoneState zone) {
		final ZoneState abstractZone = node.getState().getState().getInterpolant();
		if (abstractZone.isConsistentWith(zone)) {
			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<ItpZoneState>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<ItpZoneState>, XtaAction> parent = inEdge.getSource();

				final ZoneState B_pre = pre(zone, action, prec);
				final ZoneState A_pre = blockZone(parent, B_pre);

				final ZoneState B = zone;
				final ZoneState A = post(A_pre, action, prec);
				final ZoneState interpolant = ZoneState.interpolant(A, B);

				refine(node, interpolant);
				maintainCoverage(node, interpolant);

				return interpolant;
			} else {
				final ZoneState concreteZone = node.getState().getState().getZone();
				final ZoneState interpolant = ZoneState.interpolant(concreteZone, zone);
				refine(node, interpolant);
				maintainCoverage(node, interpolant);
				return interpolant;
			}
		} else {
			return abstractZone;
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
