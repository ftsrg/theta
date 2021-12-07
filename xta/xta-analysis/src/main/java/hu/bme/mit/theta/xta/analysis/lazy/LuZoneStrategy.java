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
import static hu.bme.mit.theta.common.Unit.unit;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.xta.analysis.zone.XtaLuZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

final class LuZoneStrategy<S extends State> implements AlgorithmStrategy<S, LuZoneState> {

	private final Lens<S, LuZoneState> lens;
	private final Analysis<LuZoneState, XtaAction, UnitPrec> analysis;
	private final Function<LuZoneState, ?> projection;

	public LuZoneStrategy(final XtaSystem system, final Lens<S, LuZoneState> lens) {
		checkNotNull(system);
		this.lens = checkNotNull(lens);
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		analysis = PrecMappingAnalysis.create(LuZoneAnalysis.create(XtaZoneAnalysis.getInstance()), p -> zonePrec);
		projection = s -> unit();
	}

	@Override
	public Analysis<LuZoneState, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Function<LuZoneState, ?> getProjection() {
		return projection;
	}

	@Override
	public boolean mightCover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer) {
		final LuZoneState covereeState = lens.get(coveree.getState());
		final LuZoneState covererState = lens.get(coverer.getState());
		return covereeState.getZone().isLeq(covererState.getZone(), covererState.getBoundFunc());
	}

	@Override
	public void cover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer,
					  final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		stats.startCloseZoneRefinement();
		final LuZoneState covererState = lens.get(coverer.getState());
		final BoundFunc boundFunc = covererState.getBoundFunc();
		propagateBounds(coveree, boundFunc, uncoveredNodes, stats);
		stats.stopCloseZoneRefinement();
	}

	@Override
	public void block(final ArgNode<S, XtaAction> node, final XtaAction action, final S succState,
					  final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		assert lens.get(succState).isBottom();
		stats.startExpandZoneRefinement();
		final BoundFunc preImage = XtaLuZoneUtils.pre(BoundFunc.top(), action);
		propagateBounds(node, preImage, uncoveredNodes, stats);
		stats.stopExpandZoneRefinement();
	}

	////

	private void propagateBounds(final ArgNode<S, XtaAction> node, final BoundFunc boundFunc,
								 final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		final LuZoneState oldState = lens.get(node.getState());
		final BoundFunc oldBoundFunc = oldState.getBoundFunc();
		if (!boundFunc.isLeq(oldBoundFunc)) {
			stats.refineZone();

			strengthen(node, boundFunc);
			maintainCoverage(node, boundFunc, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<S, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<S, XtaAction> parent = inEdge.getSource();
				final BoundFunc preBound = XtaLuZoneUtils.pre(boundFunc, action);
				propagateBounds(parent, preBound, uncoveredNodes, stats);
			}
		}
	}

	private void strengthen(final ArgNode<S, XtaAction> node, final BoundFunc boundFunc) {
		final S state = node.getState();
		final LuZoneState luZoneState = lens.get(state);
		final BoundFunc oldBoundFunc = luZoneState.getBoundFunc();
		final BoundFunc newBoundFunc = oldBoundFunc.merge(boundFunc);
		final LuZoneState newLuZoneState = luZoneState.withBoundFunc(newBoundFunc);
		final S newState = lens.set(state, newLuZoneState);
		node.setState(newState);
	}

	private void maintainCoverage(final ArgNode<S, XtaAction> node, final BoundFunc interpolant,
								  final Collection<ArgNode<S, XtaAction>> uncoveredNodes) {

		final LuZoneState covererState = lens.get(node.getState());
		final Collection<ArgNode<S, XtaAction>> uncovered = node.getCoveredNodes()
				.filter(covered -> shouldUncover(covered, covererState, interpolant)).collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	private boolean shouldUncover(final ArgNode<S, XtaAction> covered, final LuZoneState covererState,
								  final BoundFunc interpolant) {
		final LuZoneState coveredState = lens.get(covered.getState());
		return !interpolant.isLeq(coveredState.getBoundFunc())
				|| !coveredState.getZone().isLeq(covererState.getZone(), interpolant);
	}

}
