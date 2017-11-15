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
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.act.ActZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.act.ActZoneState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;
import hu.bme.mit.theta.formalism.xta.analysis.lazy.LazyXtaStatistics.Builder;
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
	public boolean covers(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> nodeToCover,
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> coveringNode) {
		return nodeToCover.getState().getState().getState2().isLeq(coveringNode.getState().getState().getState2());
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> nodeToCover,
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> coveringNode) {
		return nodeToCover.getState().getState().getState2().getZone().isLeq(coveringNode.getState().getState().getState2().getZone(),
				coveringNode.getState().getState().getState2().getActiveVars());
	}

	@Override
	public boolean shouldRefine(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> node) {
		return node.getState().getState().getState2().getZone().isBottom();
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> nodeToCover,
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> coveringNode,
			final Builder statistics) {

		final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		final Set<VarDecl<RatType>> activeVars = coveringNode.getState().getState().getState2().getActiveVars();
		propagateVars(nodeToCover, activeVars, uncoveredNodes, statistics, false);

		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> refine(
			final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> node, final Builder statistics) {

		final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		final Set<VarDecl<RatType>> activeVars = ImmutableSet.of();
		propagateVars(node, activeVars, uncoveredNodes, statistics, true);

		return uncoveredNodes;
	}

	////

	private void propagateVars(final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> node,
			final Set<VarDecl<RatType>> activeVars,
			final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes,
			final Builder statistics, final boolean forcePropagate) {

		final Set<VarDecl<RatType>> oldActiveVars = node.getState().getState().getState2().getActiveVars();

		if (forcePropagate || !oldActiveVars.containsAll(activeVars)) {
			statistics.refine();

			strengthen(node, activeVars);
			maintainCoverage(node, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction> parent = inEdge.getSource();
				final Set<VarDecl<RatType>> preActiveVars = XtaActZoneUtils.pre(activeVars, action);
				propagateVars(parent, preActiveVars, uncoveredNodes, statistics, false);
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
			final Collection<ArgNode<XtaState<Prod2State<ExplState, ActZoneState>>, XtaAction>> uncoveredNodes) {
		node.getCoveredNodes().forEach(uncoveredNodes::add);
		node.clearCoveredNodes();
	}

}
