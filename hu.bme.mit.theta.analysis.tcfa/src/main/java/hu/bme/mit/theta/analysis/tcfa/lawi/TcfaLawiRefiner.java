package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils.post;
import static hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils.pre;
import static java.util.stream.Collectors.toList;

import java.util.Collection;

import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;

public final class TcfaLawiRefiner {

	private final ZonePrecision precision;
	private final Waitlist<ArgNode<TcfaLawiState, TcfaAction>> waitlist;

	private TcfaLawiRefiner(final TCFA tcfa, final Waitlist<ArgNode<TcfaLawiState, TcfaAction>> waitlist) {
		checkNotNull(tcfa);
		this.waitlist = checkNotNull(waitlist);
		precision = ZonePrecision.create(tcfa.getClockVars());
	}

	public static TcfaLawiRefiner create(final TCFA tcfa, final Waitlist<ArgNode<TcfaLawiState, TcfaAction>> waitlist) {
		return new TcfaLawiRefiner(tcfa, waitlist);
	}

	public void enforceZone(final ArgNode<TcfaLawiState, TcfaAction> node, final ZoneState zone) {
		final Collection<ZoneState> complementZones = zone.complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(node, complementZone);
		}
	}

	private ZoneState blockZone(final ArgNode<TcfaLawiState, TcfaAction> node, final ZoneState zone) {
		final ZoneState abstractZone = node.getState().getAbstractZone();
		if (abstractZone.isConsistentWith(zone)) {
			assert node.getInEdge().isPresent();

			final ArgEdge<TcfaLawiState, TcfaAction> inEdge = node.getInEdge().get();
			final TcfaAction action = inEdge.getAction();
			final ArgNode<TcfaLawiState, TcfaAction> parent = inEdge.getSource();

			final ZoneState B_pre = pre(zone, action, precision);
			final ZoneState A_pre = blockZone(parent, B_pre);

			final ZoneState B = zone;
			final ZoneState A = post(A_pre, action, precision);
			final ZoneState interpolant = ZoneState.interpolant(A, B);

			refine(node, interpolant);
			maintainCoverage(node, interpolant);

			return interpolant;
		} else {
			return abstractZone;
		}
	}

	private void refine(final ArgNode<TcfaLawiState, TcfaAction> node, final ZoneState interpolant) {
		final ZoneState oldAbstractZone = node.getState().getAbstractZone();
		final ZoneState newAbstractZone = ZoneState.intersection(oldAbstractZone, interpolant);
		node.setState(node.getState().withAbstractZone(newAbstractZone));
	}

	private void maintainCoverage(final ArgNode<TcfaLawiState, TcfaAction> node, final ZoneState interpolant) {
		final Collection<ArgNode<TcfaLawiState, TcfaAction>> coveredNodes = node.getCoveredNodes().collect(toList());

		for (final ArgNode<TcfaLawiState, TcfaAction> coveredNode : coveredNodes) {
			final ZoneState concreteZone = coveredNode.getState().getConcreteZone();

			if (concreteZone.isLeq(interpolant)) {
				enforceZone(coveredNode, interpolant);
			} else {
				clearCoverage(coveredNode);
			}
		}
	}

	private void clearCoverage(final ArgNode<TcfaLawiState, TcfaAction> node) {
		assert node.isLeaf();
		node.unsetCoveringNode();
		node.getState().withAbstractZone(ZoneState.top());
		waitlist.add(node);
	}

}
