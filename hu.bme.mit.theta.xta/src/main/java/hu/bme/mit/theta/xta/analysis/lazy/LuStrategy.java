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
package hu.bme.mit.theta.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

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
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.xta.analysis.zone.XtaLuZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

public final class LuStrategy implements AlgorithmStrategy<Prod2State<ExplState, LuZoneState>> {

	private final Analysis<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction, UnitPrec> analysis;

	public LuStrategy(final XtaSystem system) {
		checkNotNull(system);
		analysis = createAnalysis(system);
	}

	public static LuStrategy create(final XtaSystem system) {
		return new LuStrategy(system);
	}

	////

	@Override
	public Analysis<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Partition<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>, ?> partition = Partition
				.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getState().getState1()));
		return partition;
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> coverer) {
		return coveree.getState().getState().getState2().getZone().isLeq(
				coverer.getState().getState().getState2().getZone(),
				coverer.getState().getState().getState2().getBoundFunc());
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> coverer, final Builder stats) {
		stats.startCloseZoneRefinement();
		final Collection<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		final BoundFunc boundFunc = coverer.getState().getState().getState2().getBoundFunc();
		propagateBounds(coveree, boundFunc, uncoveredNodes, stats);
		stats.stopCloseZoneRefinement();
		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> node, final XtaAction action,
			final XtaState<Prod2State<ExplState, LuZoneState>> succState, final Builder stats) {
		if (succState.getState().isBottom1()) {
			return Collections.emptyList();
		} else if (succState.getState().isBottom2()) {
			stats.startExpandZoneRefinement();
			final Collection<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
			final BoundFunc preImage = XtaLuZoneUtils.pre(BoundFunc.top(), action);
			propagateBounds(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
			return uncoveredNodes;
		} else {
			throw new AssertionError();
		}
	}

	////

	private void propagateBounds(final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> node,
			final BoundFunc boundFunc,
			final Collection<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>> uncoveredNodes,
			final Builder stats) {
		final BoundFunc oldBoundFunc = node.getState().getState().getState2().getBoundFunc();
		if (!boundFunc.isLeq(oldBoundFunc)) {
			stats.refineZone();

			strengthen(node, boundFunc);
			maintainCoverage(node, boundFunc, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> parent = inEdge.getSource();
				final BoundFunc preBound = XtaLuZoneUtils.pre(boundFunc, action);
				propagateBounds(parent, preBound, uncoveredNodes, stats);
			}
		}
	}

	private void strengthen(final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> node,
			final BoundFunc boundFunc) {
		final XtaState<Prod2State<ExplState, LuZoneState>> state = node.getState();
		final Prod2State<ExplState, LuZoneState> prodState = state.getState();
		final LuZoneState luZoneState = prodState.getState2();
		final BoundFunc oldBoundFunc = luZoneState.getBoundFunc();

		final BoundFunc newBoundFunc = oldBoundFunc.merge(boundFunc);

		final LuZoneState newLuZoneState = luZoneState.withBoundFunc(newBoundFunc);
		final Prod2State<ExplState, LuZoneState> newProdState = prodState.with2(newLuZoneState);
		final XtaState<Prod2State<ExplState, LuZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	private void maintainCoverage(final ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction> node,
			final BoundFunc interpolant,
			final Collection<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes().filter(covered -> !covered.getState().getState().getState2().getZone()
						.isLeq(node.getState().getState().getState2().getZone(), interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	////

	private static Analysis<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ExplState, XtaAction, UnitPrec> explAnalysis = XtaExplAnalysis.create(system);
		final Analysis<LuZoneState, XtaAction, ZonePrec> luZoneAnalysis = LuZoneAnalysis
				.create(XtaZoneAnalysis.getInstance());

		final Prod2Analysis<ExplState, LuZoneState, XtaAction, UnitPrec, ZonePrec> prodAnalysis = Prod2Analysis
				.create(explAnalysis, luZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod2Prec<UnitPrec, ZonePrec> prec = Prod2Prec.of(unitPrec, zonePrec);

		final Analysis<Prod2State<ExplState, LuZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod2State<ExplState, LuZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
