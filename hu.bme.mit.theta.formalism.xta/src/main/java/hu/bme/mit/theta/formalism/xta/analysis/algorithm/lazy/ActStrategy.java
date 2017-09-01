package hu.bme.mit.theta.formalism.xta.analysis.algorithm.lazy;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.act.ActZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.act.ActZoneState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;
import hu.bme.mit.theta.formalism.xta.analysis.algorithm.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaActZoneUtils;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneAnalysis;

public final class ActStrategy implements LazyXtaChecker.AlgorithmStrategy<ActZoneState> {

	private final Analysis<ActZoneState, XtaAction, UnitPrec> analysis;

	private ActStrategy(final XtaSystem system) {
		checkNotNull(system);
		final ZonePrec prec = ZonePrec.of(system.getClockVars());
		analysis = PrecMappingAnalysis.create(ActZoneAnalysis.create(XtaZoneAnalysis.getInstance()), u -> prec);
	}

	public static ActStrategy create(final XtaSystem system) {
		return new ActStrategy(system);
	}

	@Override
	public Analysis<ActZoneState, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public boolean covers(final ArgNode<XtaState<ActZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ActZoneState>, XtaAction> coveringNode) {
		return nodeToCover.getState().getState().isLeq(coveringNode.getState().getState());
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<ActZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ActZoneState>, XtaAction> coveringNode) {
		return nodeToCover.getState().getState().getZone().isLeq(coveringNode.getState().getState().getZone(),
				coveringNode.getState().getState().getActiveVars());
	}

	@Override
	public boolean shouldRefine(final ArgNode<XtaState<ActZoneState>, XtaAction> node) {
		return node.getState().getState().getZone().isBottom();
	}

	@Override
	public Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> forceCover(
			final ArgNode<XtaState<ActZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ActZoneState>, XtaAction> coveringNode, final Builder statistics) {

		final Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> uncoveredNodes = new ArrayList<>();
		final Set<VarDecl<RatType>> activeVars = coveringNode.getState().getState().getActiveVars();
		propagateVars(nodeToCover, activeVars, uncoveredNodes, statistics, false);

		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> refine(
			final ArgNode<XtaState<ActZoneState>, XtaAction> node, final Builder statistics) {

		final Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> uncoveredNodes = new ArrayList<>();
		final Set<VarDecl<RatType>> activeVars = ImmutableSet.of();
		propagateVars(node, activeVars, uncoveredNodes, statistics, true);

		return uncoveredNodes;
	}

	@Override
	public void resetState(final ArgNode<XtaState<ActZoneState>, XtaAction> node) {
		final ActZoneState newLuState = node.getState().getState().withActiveVars(ImmutableSet.of());
		node.setState(node.getState().withState(newLuState));
	}

	////

	private void propagateVars(final ArgNode<XtaState<ActZoneState>, XtaAction> node,
			final Set<VarDecl<RatType>> activeVars,
			final Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> uncoveredNodes, final Builder statistics,
			final boolean forcePropagate) {

		final Set<VarDecl<RatType>> oldActiveVars = node.getState().getState().getActiveVars();

		if (forcePropagate || !oldActiveVars.containsAll(activeVars)) {
			statistics.refine();

			strengthen(node, activeVars);
			maintainCoverage(node, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<ActZoneState>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<ActZoneState>, XtaAction> parent = inEdge.getSource();
				final Set<VarDecl<RatType>> preActiveVars = XtaActZoneUtils.pre(activeVars, action);
				propagateVars(parent, preActiveVars, uncoveredNodes, statistics, false);
			}
		}
	}

	private void strengthen(final ArgNode<XtaState<ActZoneState>, XtaAction> node,
			final Set<VarDecl<RatType>> activeVars) {
		final Set<VarDecl<RatType>> oldActiveVars = node.getState().getState().getActiveVars();
		final Set<VarDecl<RatType>> newActiveVars = Sets.union(oldActiveVars, activeVars);
		final ActZoneState newActState = node.getState().getState().withActiveVars(newActiveVars);
		node.setState(node.getState().withState(newActState));
	}

	private void maintainCoverage(final ArgNode<XtaState<ActZoneState>, XtaAction> node,
			final Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> uncoveredNodes) {
		node.getCoveredNodes().forEach(n -> uncoveredNodes.add(n));
		node.clearCoveredNodes();
	}

}
