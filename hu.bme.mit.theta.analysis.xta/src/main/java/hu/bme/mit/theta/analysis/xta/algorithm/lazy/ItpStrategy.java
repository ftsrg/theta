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

public abstract class ItpStrategy implements LazyXtaChecker.AlgorithmStrategy<ItpZoneState> {

	public enum ItpOperator {

		DEFAULT {
			@Override
			public ZoneState interpolate(final ZoneState zoneA, final ZoneState zoneB) {
				return ZoneState.interpolant(zoneA, zoneB);
			}
		},

		WEAK {
			@Override
			public ZoneState interpolate(final ZoneState zoneA, final ZoneState zoneB) {
				return ZoneState.weakInterpolant(zoneA, zoneB);
			}
		};

		public abstract ZoneState interpolate(final ZoneState zoneA, final ZoneState zoneB);

	}

	private final ZonePrec prec;
	private final Analysis<ItpZoneState, XtaAction, UnitPrec> analysis;
	private final ItpOperator operator;

	ItpStrategy(final XtaSystem system, final ItpOperator operator) {
		checkNotNull(system);
		this.operator = checkNotNull(operator);
		prec = ZonePrec.of(system.getClockVars());
		analysis = PrecMappingAnalysis.create(ItpZoneAnalysis.create(XtaZoneAnalysis.getInstance()), u -> prec);
	}

	////

	protected final ZoneState interpolate(final ZoneState zoneA, final ZoneState zoneB) {
		return operator.interpolate(zoneA, zoneB);
	}

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
