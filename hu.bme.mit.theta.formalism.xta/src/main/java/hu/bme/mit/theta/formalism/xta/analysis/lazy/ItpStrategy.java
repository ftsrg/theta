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
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;
import hu.bme.mit.theta.formalism.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneUtils;

public abstract class ItpStrategy implements AlgorithmStrategy<Prod2State<ExplState, ItpZoneState>> {

	private final ZonePrec prec;
	private final Analysis<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction, UnitPrec> analysis;

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

	protected final void strengthen(final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> node,
			final ZoneState interpolant) {
		final XtaState<Prod2State<ExplState, ItpZoneState>> state = node.getState();
		final Prod2State<ExplState, ItpZoneState> prodState = state.getState();
		final ItpZoneState itpZoneState = prodState.getState2();
		final ZoneState abstractZoneState = itpZoneState.getInterpolant();

		final ZoneState newAbstractZone = ZoneState.intersection(abstractZoneState, interpolant);

		final ItpZoneState newItpZoneState = itpZoneState.withInterpolant(newAbstractZone);
		final Prod2State<ExplState, ItpZoneState> newProdState = prodState.with2(newItpZoneState);
		final XtaState<Prod2State<ExplState, ItpZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	protected final void maintainCoverage(final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> node,
			final ZoneState interpolant,
			final Collection<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes()
				.filter(covered -> !covered.getState().getState().getState2().getInterpolant().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	protected abstract ZoneState blockZone(final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> node,
			final ZoneState zone,
			final Collection<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats);

	////

	@Override
	public final Analysis<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Partition<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>, ?> partition = Partition
				.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getState().getState1()));
		return partition;
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> coverer) {
		final ZoneState covereeZone = coveree.getState().getState().getState2().getZone();
		final ZoneState covererZone = coverer.getState().getState().getState2().getInterpolant();
		return covereeZone.isLeq(covererZone);
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> coverer,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();

		stats.startCloseZoneRefinement();
		final Collection<ZoneState> complementZones = coverer.getState().getState().getState2().getInterpolant()
				.complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(coveree, complementZone, uncoveredNodes, stats);
		}
		stats.stopCloseZoneRefinement();

		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction> node, final XtaAction action,
			final XtaState<Prod2State<ExplState, ItpZoneState>> succState, final LazyXtaStatistics.Builder stats) {
		if (succState.getState().isBottom1()) {
			return Collections.emptyList();
		} else if (succState.getState().isBottom2()) {
			stats.startExpandZoneRefinement();
			final Collection<ArgNode<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
			final ZoneState preImage = pre(ZoneState.top(), action);
			blockZone(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
			return uncoveredNodes;
		} else {
			throw new AssertionError();
		}
	}

	////

	private static Analysis<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ExplState, XtaAction, UnitPrec> concreteExplAnalysis = XtaExplAnalysis.create(system);
		final Analysis<ItpZoneState, XtaAction, ZonePrec> itpZoneAnalysis = ItpZoneAnalysis
				.create(XtaZoneAnalysis.getInstance());

		final Prod2Analysis<ExplState, ItpZoneState, XtaAction, UnitPrec, ZonePrec> prodAnalysis = Prod2Analysis
				.create(concreteExplAnalysis, itpZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod2Prec<UnitPrec, ZonePrec> prec = Prod2Prec.of(unitPrec, zonePrec);

		final Analysis<Prod2State<ExplState, ItpZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod2State<ExplState, ItpZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
