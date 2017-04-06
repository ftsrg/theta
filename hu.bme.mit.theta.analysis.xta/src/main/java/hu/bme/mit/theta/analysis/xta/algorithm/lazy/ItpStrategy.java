package hu.bme.mit.theta.analysis.xta.algorithm.lazy;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.analysis.xta.zone.XtaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

abstract class ItpStrategy implements LazyXtaChecker.AlgorithmStrategy<ItpZoneState> {

	private final ZonePrec prec;
	private final Analysis<ItpZoneState, XtaAction, UnitPrec> analysis;

	protected ItpStrategy(final XtaSystem system) {
		checkNotNull(system);
		prec = ZonePrec.of(system.getClocks());
		analysis = PrecMappingAnalysis.create(ItpZoneAnalysis.create(XtaZoneAnalysis.getInstance()), u -> prec);
	}

	////

	protected final ZoneState pre(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.pre(state, action, prec);
	}

	protected final ZoneState post(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.post(state, action, prec);
	}

	protected final void strengthen(final ArgNode<XtaState<ItpZoneState>, XtaAction> node,
			final ZoneState interpolant) {
		final ZoneState oldAbstractZone = node.getState().getState().getInterpolant();
		final ZoneState newAbstractZone = ZoneState.intersection(oldAbstractZone, interpolant);
		final ItpZoneState newItpState = node.getState().getState().withInterpolant(newAbstractZone);
		node.setState(node.getState().withState(newItpState));
	}

	protected final void maintainCoverage(final ArgNode<XtaState<ItpZoneState>, XtaAction> node,
			final Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> uncoveredNodes) {
		node.getCoveredNodes().forEach(n -> uncoveredNodes.add(n));
		node.clearCoveredNodes();
	}

	////

	@Override
	public final Analysis<ItpZoneState, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public final boolean covers(final ArgNode<XtaState<ItpZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ItpZoneState>, XtaAction> coveringNode) {
		return nodeToCover.getState().getState().isLeq(coveringNode.getState().getState());
	}

	@Override
	public final boolean mightCover(final ArgNode<XtaState<ItpZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ItpZoneState>, XtaAction> coveringNode) {
		return nodeToCover.getState().getState().getZone().isLeq(coveringNode.getState().getState().getInterpolant());
	}

	@Override
	public final boolean shouldRefine(final ArgNode<XtaState<ItpZoneState>, XtaAction> node) {
		return node.getState().getState().getZone().isBottom();
	}

	@Override
	public final void resetState(final ArgNode<XtaState<ItpZoneState>, XtaAction> node) {
		final ItpZoneState newItpState = node.getState().getState().withInterpolant(ZoneState.top());
		node.setState(node.getState().withState(newItpState));
	}

}
