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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.xta.analysis.expl.itp.ItpExplAnalysis;
import hu.bme.mit.theta.xta.analysis.expl.itp.ItpExplState;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneState;

public final class ExplItpStrategy implements AlgorithmStrategy<Prod2State<ItpExplState, ItpZoneState>> {

	private final ItpExplRefiner explRefiner;
	private final ItpZoneRefiner zoneRefiner;
	private final Analysis<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction, UnitPrec> analysis;
	private final ZonePrec prec;

	private ExplItpStrategy(final XtaSystem system, final ItpExplRefiner explRefiner,
			final ItpZoneRefiner zoneRefiner) {
		checkNotNull(system);
		this.explRefiner = checkNotNull(explRefiner);
		this.zoneRefiner = checkNotNull(zoneRefiner);
		analysis = createAnalysis(system);
		prec = ZonePrec.of(system.getClockVars());
	}

	public static ExplItpStrategy createForward(final XtaSystem system) {
		return new ExplItpStrategy(system, BwItpExplRefiner.getInstance(), new FwItpZoneRefiner(system));
	}

	public static ExplItpStrategy createBackward(final XtaSystem system) {
		return new ExplItpStrategy(system, BwItpExplRefiner.getInstance(), new BwItpZoneRefiner(system));
	}

	@Override
	public final Analysis<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public final Partition<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>, List<Loc>> partition = Partition
				.of(n -> n.getState().getLocs());
		return partition;
	}

	@Override
	public final boolean mightCover(final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> coverer) {
		final ExplState covereeExpl = coveree.getState().getState().getState1().getConcrState();
		final ExplState covererExpl = coverer.getState().getState().getState1().getAbstrState();
		final ZoneState covereeZone = coveree.getState().getState().getState2().getConcrState();
		final ZoneState covererZone = coverer.getState().getState().getState2().getAbstrState();
		return covereeExpl.isLeq(covererExpl) && covereeZone.isLeq(covererZone);
	}

	@Override
	public final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> coverer,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();

		stats.startCloseExplRefinement();
		explRefiner.blockExpl(coveree, Not(coverer.getState().getState().getState1().toExpr()), uncoveredNodes, stats);
		stats.stopCloseExplRefinement();

		stats.startCloseZoneRefinement();
		final Collection<ZoneState> complementZones = coverer.getState().getState().getState2().getAbstrState()
				.complement();
		for (final ZoneState complementZone : complementZones) {
			zoneRefiner.blockZone(coveree, complementZone, uncoveredNodes, stats);
		}
		stats.stopCloseZoneRefinement();

		return uncoveredNodes;
	}

	@Override
	public final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> node, final XtaAction action,
			final XtaState<Prod2State<ItpExplState, ItpZoneState>> succState, final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		if (succState.getState().isBottom1()) {
			stats.startExpandExplRefinement();
			final Expr<BoolType> preImage = XtaDataUtils.pre(True(), action);
			explRefiner.blockExpl(node, preImage, uncoveredNodes, stats);
			stats.stopExpandExplRefinement();
		} else if (succState.getState().isBottom2()) {
			stats.startExpandZoneRefinement();
			final ZoneState preImage = XtaZoneUtils.pre(ZoneState.top(), action, prec);
			zoneRefiner.blockZone(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
		} else {
			throw new AssertionError();
		}
		return uncoveredNodes;
	}

	////

	private static Analysis<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ItpExplState, XtaAction, UnitPrec> itpExplAnalysis = ItpExplAnalysis
				.create(XtaExplAnalysis.create(system));
		final Analysis<ItpZoneState, XtaAction, ZonePrec> itpZoneAnalysis = ItpZoneAnalysis
				.create(XtaZoneAnalysis.getInstance());

		final Prod2Analysis<ItpExplState, ItpZoneState, XtaAction, UnitPrec, ZonePrec> prodAnalysis = Prod2Analysis
				.create(itpExplAnalysis, itpZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod2Prec<UnitPrec, ZonePrec> prec = Prod2Prec.of(unitPrec, zonePrec);

		final Analysis<Prod2State<ItpExplState, ItpZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
