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

import java.util.Collection;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneState;

abstract class ItpZoneRefiner {

	private final ZonePrec prec;

	public ItpZoneRefiner(final XtaSystem system) {
		checkNotNull(system);
		prec = ZonePrec.of(system.getClockVars());
	}

	public abstract <S extends State> ZoneState blockZone(
			final ArgNode<XtaState<Prod2State<S, ItpZoneState>>, XtaAction> node, final ZoneState zone,
			final Collection<ArgNode<XtaState<Prod2State<S, ItpZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats);

	public final ZoneState pre(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.pre(state, action, prec);
	}

	public final ZoneState post(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.post(state, action, prec);
	}

	protected final <S extends State> void strengthen(
			final ArgNode<XtaState<Prod2State<S, ItpZoneState>>, XtaAction> node, final ZoneState interpolant) {
		final XtaState<Prod2State<S, ItpZoneState>> state = node.getState();
		final Prod2State<S, ItpZoneState> prodState = state.getState();
		final ItpZoneState itpZoneState = prodState.getState2();
		final ZoneState abstrZoneState = itpZoneState.getAbstrState();

		final ZoneState newAbstrZone = ZoneState.intersection(abstrZoneState, interpolant);

		final ItpZoneState newItpZoneState = itpZoneState.withAbstrState(newAbstrZone);
		final Prod2State<S, ItpZoneState> newProdState = prodState.with2(newItpZoneState);
		final XtaState<Prod2State<S, ItpZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	protected final <S extends State> void maintainCoverage(
			final ArgNode<XtaState<Prod2State<S, ItpZoneState>>, XtaAction> node, final ZoneState interpolant,
			final Collection<ArgNode<XtaState<Prod2State<S, ItpZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<S, ItpZoneState>>, XtaAction>> uncovered = node.getCoveredNodes()
				.filter(covered -> !covered.getState().getState().getState2().getAbstrState().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

}
