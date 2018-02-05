/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.formalism.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.act.ActZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.act.ActZoneState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;
import hu.bme.mit.theta.formalism.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaActZoneUtils;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneAnalysis;

public final class ActStrategy implements AlgorithmStrategy<Prod2State<ExplState, ActZoneState>> {

	private final Analysis<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction, UnitPrec> analysis;

	private ActStrategy(final XtaSystem system) {
		checkNotNull(system);
		analysis = createAnalysis(system);
	}

	public static ActStrategy create(final XtaSystem system) {
		return new ActStrategy(system);
	}

	@Override
	public Analysis<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Partition<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>, ?> partition = Partition
				.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getState().getState1()));
		return partition;
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> coverer) {
		return coveree.getState().getState().getState2().getZone().isLeq(
				coverer.getState().getState().getState2().getZone(),
				coverer.getState().getState().getState2().getActiveVars());
	}

	@Override
	public boolean shouldExclude(final XtaState<Prod2State<ExplState, ActZoneState>> state) {
		return state.getState().isBottom1() || state.getState().isBottom2();
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> coverer, final Builder stats) {
		stats.startCloseZoneRefinement();
		final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		final Set<VarDecl<RatType>> activeVars = coverer.getState().getState().getState2().getActiveVars();
		propagateVars(coveree, activeVars, uncoveredNodes, stats);
		stats.stopCloseZoneRefinement();
		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> node, final XtaAction action,
			final XtaState<Prod2State<ExplState, ActZoneState>> succState, final Builder stats) {

		final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		if (succState.getState().isBottom1()) {
			// do nothing
		} else if (succState.getState().isBottom2()) {
			stats.startExpandZoneRefinement();
			final Set<VarDecl<RatType>> preImage = XtaActZoneUtils.pre(ImmutableSet.of(), action);
			propagateVars(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
		} else {
			throw new AssertionError();
		}
		return uncoveredNodes;
	}

	////

	private void propagateVars(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> node,
			final Set<VarDecl<RatType>> activeVars,
			final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes,
			final Builder stats) {

		final Set<VarDecl<RatType>> oldActiveVars = node.getState().getState().getState2().getActiveVars();

		if (!oldActiveVars.containsAll(activeVars)) {
			stats.refineZone();

			strengthen(node, activeVars);
			maintainCoverage(node, activeVars, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> parent = inEdge.getSource();
				final Set<VarDecl<RatType>> preActiveVars = XtaActZoneUtils.pre(activeVars, action);
				propagateVars(parent, preActiveVars, uncoveredNodes, stats);
			}
		}
	}

	private void strengthen(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> node,
			final Set<VarDecl<RatType>> activeVars) {
		final XtaState<Prod2State<ExplState, ActZoneState>> state = node.getState();
		final Prod2State<ExplState, ActZoneState> prodState = state.getState();
		final ActZoneState actZoneState = prodState.getState2();
		final Set<VarDecl<RatType>> oldActiveVars = actZoneState.getActiveVars();

		final Set<VarDecl<RatType>> newActiveVars = Sets.union(oldActiveVars, activeVars);

		final ActZoneState newActZoneState = actZoneState.withActiveVars(newActiveVars);
		final Prod2State<ExplState, ActZoneState> newProdState = prodState.with2(newActZoneState);
		final XtaState<Prod2State<ExplState, ActZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	private void maintainCoverage(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> node,
			final Set<VarDecl<RatType>> interpolant,
			final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes().filter(covered -> !covered.getState().getState().getState2().getZone()
						.isLeq(node.getState().getState().getState2().getZone(), interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	////

	private static Analysis<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ExplState, XtaAction, UnitPrec> explAnalysis = XtaExplAnalysis.create(system);
		final Analysis<ActZoneState, XtaAction, ZonePrec> actZoneAnalysis = ActZoneAnalysis
				.create(XtaZoneAnalysis.getInstance());

		final Prod2Analysis<ExplState, ActZoneState, XtaAction, UnitPrec, ZonePrec> prodAnalysis = Prod2Analysis
				.create(explAnalysis, actZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod2Prec<UnitPrec, ZonePrec> prec = Prod2Prec.of(unitPrec, zonePrec);

		final Analysis<Prod2State<ExplState, ActZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
