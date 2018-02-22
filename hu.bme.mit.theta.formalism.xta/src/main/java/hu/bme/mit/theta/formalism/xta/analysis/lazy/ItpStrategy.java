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
import java.util.Collections;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.prod3.Prod3Analysis;
import hu.bme.mit.theta.analysis.prod3.Prod3Prec;
import hu.bme.mit.theta.analysis.prod3.Prod3State;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZoneOrd;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;
import hu.bme.mit.theta.formalism.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneUtils;

public abstract class ItpStrategy implements AlgorithmStrategy<Prod3State<ExplState, ZoneState, ZoneState>> {

	private final ZonePrec prec;
	private final Analysis<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction, UnitPrec> analysis;

	ItpStrategy(final XtaSystem system) {
		checkNotNull(system);
		prec = ZonePrec.of(system.getClockVars());
		analysis = createAnalysis(system);
	}

	////

	protected final ZoneState interpolate(final ZoneState zoneA, final ZoneState zoneB) {
		return ZoneState.interpolant(zoneA, zoneB);
	}

	protected final ZoneState pre(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.pre(state, action, prec);
	}

	protected final ZoneState post(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.post(state, action, prec);
	}

	protected final void strengthen(
			final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> node,
			final ZoneState interpolant) {
		final XtaState<Prod3State<ExplState, ZoneState, ZoneState>> state = node.getState();
		final Prod3State<ExplState, ZoneState, ZoneState> prodState = state.getState();
		final ZoneState abstractZone = prodState.getState3();

		final ZoneState newAbstractZone = ZoneState.intersection(abstractZone, interpolant);

		final Prod3State<ExplState, ZoneState, ZoneState> newProdState = prodState.with3(newAbstractZone);
		final XtaState<Prod3State<ExplState, ZoneState, ZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	protected final void maintainCoverage(
			final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> node,
			final ZoneState interpolant,
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes().filter(covered -> !covered.getState().getState().getState3().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	protected abstract ZoneState blockZone(
			final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> node, final ZoneState zone,
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats);

	////

	@Override
	public final Analysis<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Partition<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>, ?> partition = Partition
				.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getState().getState1()));
		return partition;
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> coverer) {
		final ZoneState covereeZone = coveree.getState().getState().getState2();
		final ZoneState covererZone = coverer.getState().getState().getState3();
		return covereeZone.isLeq(covererZone);
	}

	@Override
	public boolean shouldExclude(final XtaState<Prod3State<ExplState, ZoneState, ZoneState>> state) {
		return state.getState().isBottom1() || state.getState().isBottom2();
	}

	@Override
	public Collection<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> coverer,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();

		stats.startCloseZoneRefinement();
		final Collection<ZoneState> complementZones = coverer.getState().getState().getState3().complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(coveree, complementZone, uncoveredNodes, stats);
		}
		stats.stopCloseZoneRefinement();

		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction> node,
			final XtaAction action, final XtaState<Prod3State<ExplState, ZoneState, ZoneState>> succState,
			final LazyXtaStatistics.Builder stats) {
		if (succState.getState().isBottom1()) {
			return Collections.emptyList();
		} else if (succState.getState().isBottom2()) {
			stats.startExpandZoneRefinement();
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
			final ZoneState preImage = pre(ZoneState.top(), action);
			blockZone(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
			return uncoveredNodes;
		} else {
			throw new AssertionError();
		}
	}

	////

	private static Analysis<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ExplState, XtaAction, UnitPrec> concreteExplAnalysis = XtaExplAnalysis.create(system);
		final Analysis<ZoneState, XtaAction, ZonePrec> concreteZoneAnalysis = XtaZoneAnalysis.getInstance();
		final Analysis<ZoneState, XtaAction, UnitPrec> abstractZoneAnalysis = TopAnalysis.create(ZoneState.top(),
				ZoneOrd.getInstance());

		final Prod3Analysis<ExplState, ZoneState, ZoneState, XtaAction, UnitPrec, ZonePrec, UnitPrec> prodAnalysis = Prod3Analysis
				.create(concreteExplAnalysis, concreteZoneAnalysis, abstractZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod3Prec<UnitPrec, ZonePrec, UnitPrec> prec = Prod3Prec.of(unitPrec, zonePrec, unitPrec);

		final Analysis<Prod3State<ExplState, ZoneState, ZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod3State<ExplState, ZoneState, ZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
