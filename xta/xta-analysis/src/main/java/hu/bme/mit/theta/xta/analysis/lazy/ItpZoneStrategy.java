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
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneState;

abstract class ItpZoneStrategy<S extends State> implements AlgorithmStrategy<S, ItpZoneState> {

	private final Lens<S, ItpZoneState> lens;
	private final ZonePrec prec;
	private final Analysis<ItpZoneState, XtaAction, UnitPrec> analysis;
	private final Function<ItpZoneState, ?> projection;

	public ItpZoneStrategy(final XtaSystem system, final Lens<S, ItpZoneState> lens) {
		checkNotNull(system);
		this.lens = checkNotNull(lens);
		prec = ZonePrec.of(system.getClockVars());
		analysis = PrecMappingAnalysis.create(ItpZoneAnalysis.create(XtaZoneAnalysis.getInstance()), p -> prec);
		projection = s -> unit();
	}

	@Override
	public final Analysis<ItpZoneState, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public final Function<ItpZoneState, ?> getProjection() {
		return projection;
	}

	@Override
	public final boolean mightCover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer) {
		final ZoneState covereeZone = lens.get(coveree.getState()).getConcrState();
		final ZoneState covererZone = lens.get(coverer.getState()).getAbstrState();
		return covereeZone.isLeq(covererZone);
	}

	@Override
	public final void cover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer,
							final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		stats.startCloseZoneRefinement();
		final ItpZoneState covererState = lens.get(coverer.getState());
		final Collection<ZoneState> complementZones = covererState.getAbstrState().complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(coveree, complementZone, uncoveredNodes, stats);
		}
		stats.stopCloseZoneRefinement();
	}

	@Override
	public final void block(final ArgNode<S, XtaAction> node, final XtaAction action, final S succState,
							final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		assert lens.get(succState).isBottom();
		stats.startExpandZoneRefinement();
		final ZoneState preImage = pre(ZoneState.top(), action);
		blockZone(node, preImage, uncoveredNodes, stats);
		stats.stopExpandZoneRefinement();
	}

	////

	protected abstract ZoneState blockZone(final ArgNode<S, XtaAction> node, final ZoneState zone,
										   final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats);

	protected final Lens<S, ItpZoneState> getLens() {
		return lens;
	}

	protected final ZoneState pre(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.pre(state, action, prec);
	}

	protected final ZoneState post(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.post(state, action, prec);
	}

	protected final void strengthen(final ArgNode<S, XtaAction> node, final ZoneState interpolant) {
		final S state = node.getState();
		final ItpZoneState itpZoneState = lens.get(state);
		final ZoneState abstrZoneState = itpZoneState.getAbstrState();
		final ZoneState newAbstrZone = ZoneState.intersection(abstrZoneState, interpolant);
		final ItpZoneState newItpZoneState = itpZoneState.withAbstrState(newAbstrZone);
		final S newState = lens.set(state, newItpZoneState);
		node.setState(newState);
	}

	protected final void maintainCoverage(final ArgNode<S, XtaAction> node, final ZoneState interpolant,
										  final Collection<ArgNode<S, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<S, XtaAction>> uncovered = node.getCoveredNodes()
				.filter(covered -> shouldUncover(covered, interpolant)).collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	private boolean shouldUncover(final ArgNode<S, XtaAction> covered, final ZoneState interpolant) {
		final ItpZoneState coveredState = lens.get(covered.getState());
		return !coveredState.getAbstrState().isLeq(interpolant);
	}

}
