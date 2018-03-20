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
import hu.bme.mit.theta.analysis.zone.BoundFunc;
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
import hu.bme.mit.theta.xta.analysis.zone.XtaLuZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

public final class ExplLuStrategy implements AlgorithmStrategy<Prod2State<ItpExplState, LuZoneState>> {

	private final ItpExplRefiner explRefiner;
	private final Analysis<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction, UnitPrec> analysis;

	private ExplLuStrategy(final XtaSystem system, final ItpExplRefiner explRefiner) {
		checkNotNull(system);
		this.explRefiner = checkNotNull(explRefiner);
		analysis = createAnalysis(system);
	}

	public static ExplLuStrategy create(final XtaSystem system) {
		return new ExplLuStrategy(system, BwItpExplRefiner.getInstance());
	}

	@Override
	public Analysis<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Partition<ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction>, List<Loc>> partition = Partition
				.of(n -> n.getState().getLocs());
		return partition;
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction> coverer) {
		final ExplState covereeExpl = coveree.getState().getState().getState1().getConcrState();
		final ExplState covererExpl = coverer.getState().getState().getState1().getAbstrState();
		final ZoneState covereeZone = coveree.getState().getState().getState2().getZone();
		final ZoneState covererZone = coverer.getState().getState().getState2().getZone();
		final BoundFunc covererBoundFunc = coverer.getState().getState().getState2().getBoundFunc();
		return covereeExpl.isLeq(covererExpl) && covereeZone.isLeq(covererZone, covererBoundFunc);
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction> coverer,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();

		stats.startCloseExplRefinement();
		explRefiner.blockExpl(coveree, Not(coverer.getState().getState().getState1().toExpr()), uncoveredNodes, stats);
		stats.stopCloseExplRefinement();

		stats.startCloseZoneRefinement();
		final BoundFunc boundFunc = coverer.getState().getState().getState2().getBoundFunc();
		LuZoneRefiner.getInstance().propagateBounds(coveree, boundFunc, uncoveredNodes, stats);
		stats.stopCloseZoneRefinement();

		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction> node, final XtaAction action,
			final XtaState<Prod2State<ItpExplState, LuZoneState>> succState, final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		if (succState.getState().isBottom1()) {
			stats.startExpandExplRefinement();
			final Expr<BoolType> preImage = XtaDataUtils.pre(True(), action);
			explRefiner.blockExpl(node, preImage, uncoveredNodes, stats);
			stats.stopExpandExplRefinement();
		} else if (succState.getState().isBottom2()) {
			stats.startExpandZoneRefinement();
			final BoundFunc preImage = XtaLuZoneUtils.pre(BoundFunc.top(), action);
			LuZoneRefiner.getInstance().propagateBounds(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
		} else {
			throw new AssertionError();
		}
		return uncoveredNodes;
	}

	////

	private static Analysis<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ItpExplState, XtaAction, UnitPrec> itpExplAnalysis = ItpExplAnalysis
				.create(XtaExplAnalysis.create(system));
		final Analysis<LuZoneState, XtaAction, ZonePrec> luZoneAnalysis = LuZoneAnalysis
				.create(XtaZoneAnalysis.getInstance());

		final Prod2Analysis<ItpExplState, LuZoneState, XtaAction, UnitPrec, ZonePrec> prodAnalysis = Prod2Analysis
				.create(itpExplAnalysis, luZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod2Prec<UnitPrec, ZonePrec> prec = Prod2Prec.of(unitPrec, zonePrec);

		final Analysis<Prod2State<ItpExplState, LuZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod2State<ItpExplState, LuZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
