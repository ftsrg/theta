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

import static java.util.stream.Collectors.toList;

import java.util.Collection;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.xta.analysis.zone.XtaLuZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

final class LuZoneRefiner {

	private LuZoneRefiner() {
	}

	private static class LazyHolder {
		static final LuZoneRefiner INSTANCE = new LuZoneRefiner();
	}

	public static LuZoneRefiner getInstance() {
		return LazyHolder.INSTANCE;
	}

	public <S extends State> void propagateBounds(final ArgNode<XtaState<Prod2State<S, LuZoneState>>, XtaAction> node,
			final BoundFunc boundFunc,
			final Collection<ArgNode<XtaState<Prod2State<S, LuZoneState>>, XtaAction>> uncoveredNodes,
			final Builder stats) {
		final BoundFunc oldBoundFunc = node.getState().getState().getState2().getBoundFunc();
		if (!boundFunc.isLeq(oldBoundFunc)) {
			stats.refineZone();

			strengthen(node, boundFunc);
			maintainCoverage(node, boundFunc, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<Prod2State<S, LuZoneState>>, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<Prod2State<S, LuZoneState>>, XtaAction> parent = inEdge.getSource();
				final BoundFunc preBound = XtaLuZoneUtils.pre(boundFunc, action);
				propagateBounds(parent, preBound, uncoveredNodes, stats);
			}
		}
	}

	private <S extends State> void strengthen(final ArgNode<XtaState<Prod2State<S, LuZoneState>>, XtaAction> node,
			final BoundFunc boundFunc) {
		final XtaState<Prod2State<S, LuZoneState>> state = node.getState();
		final Prod2State<S, LuZoneState> prodState = state.getState();
		final LuZoneState luZoneState = prodState.getState2();
		final BoundFunc oldBoundFunc = luZoneState.getBoundFunc();

		final BoundFunc newBoundFunc = oldBoundFunc.merge(boundFunc);

		final LuZoneState newLuZoneState = luZoneState.withBoundFunc(newBoundFunc);
		final Prod2State<S, LuZoneState> newProdState = prodState.with2(newLuZoneState);
		final XtaState<Prod2State<S, LuZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	private <S extends State> void maintainCoverage(final ArgNode<XtaState<Prod2State<S, LuZoneState>>, XtaAction> node,
			final BoundFunc interpolant,
			final Collection<ArgNode<XtaState<Prod2State<S, LuZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<S, LuZoneState>>, XtaAction>> uncovered = node.getCoveredNodes()
				.filter(covered -> !interpolant.isLeq(covered.getState().getState().getState2().getBoundFunc())
						|| !covered.getState().getState().getState2().getZone()
								.isLeq(node.getState().getState().getState2().getZone(), interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

}
