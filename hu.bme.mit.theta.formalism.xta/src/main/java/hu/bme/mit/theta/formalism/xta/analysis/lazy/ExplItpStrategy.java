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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.prod4.Prod4Analysis;
import hu.bme.mit.theta.analysis.prod4.Prod4Prec;
import hu.bme.mit.theta.analysis.prod4.Prod4State;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZoneOrd;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.ImmutableValuation.Builder;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;
import hu.bme.mit.theta.formalism.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneUtils;

public abstract class ExplItpStrategy
		implements AlgorithmStrategy<Prod4State<ExplState, ZoneState, ExplState, ZoneState>> {

	private final Analysis<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction, UnitPrec> analysis;
	private final ZonePrec prec;

	protected ExplItpStrategy(final XtaSystem system) {
		checkNotNull(system);
		analysis = createAnalysis(system);
		prec = ZonePrec.of(system.getClockVars());
	}

	protected abstract ZoneState blockZone(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> node,
			final ZoneState zone,
			final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats);

	////

	protected final ZoneState pre(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.pre(state, action, prec);
	}

	protected final ZoneState post(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.post(state, action, prec);
	}

	protected final void strengthenZone(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> node,
			final ZoneState interpolant) {
		final XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>> state = node.getState();
		final Prod4State<ExplState, ZoneState, ExplState, ZoneState> prodState = state.getState();
		final ZoneState abstractZone = prodState.getState4();

		final ZoneState newAbstractZone = ZoneState.intersection(abstractZone, interpolant);

		final Prod4State<ExplState, ZoneState, ExplState, ZoneState> newProdState = prodState.with4(newAbstractZone);
		final XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	protected final void maintainZoneCoverage(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> node,
			final ZoneState interpolant,
			final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes().filter(covered -> !covered.getState().getState().getState4().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	////

	@Override
	public final Analysis<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public final Partition<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>, List<Loc>> partition = Partition
				.of(n -> n.getState().getLocs());
		return partition;
	}

	@Override
	public final boolean mightCover(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> coverer) {
		final ExplState covereeExpl = coveree.getState().getState().getState1();
		final ExplState covererExpl = coverer.getState().getState().getState3();
		final ZoneState covereeZone = coveree.getState().getState().getState2();
		final ZoneState covererZone = coverer.getState().getState().getState4();
		return covereeExpl.isLeq(covererExpl) && covereeZone.isLeq(covererZone);
	}

	@Override
	public final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> coverer,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();

		stats.startCloseExplRefinement();
		blockExpl(coveree, Not(coverer.getState().getState().getState3().toExpr()), uncoveredNodes, stats);
		stats.stopCloseExplRefinement();

		stats.startCloseZoneRefinement();
		final Collection<ZoneState> complementZones = coverer.getState().getState().getState4().complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(coveree, complementZone, uncoveredNodes, stats);
		}
		stats.stopCloseZoneRefinement();

		return uncoveredNodes;
	}

	@Override
	public final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> node,
			final XtaAction action, final XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>> succState,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		if (succState.getState().isBottom1()) {
			stats.startExpandExplRefinement();
			final Expr<BoolType> preImage = XtaDataUtils.pre(True(), action);
			blockExpl(node, preImage, uncoveredNodes, stats);
			stats.stopExpandExplRefinement();
		} else if (succState.getState().isBottom2()) {
			stats.startExpandZoneRefinement();
			final ZoneState preImage = XtaZoneUtils.pre(ZoneState.top(), action, prec);
			blockZone(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
		} else {
			throw new AssertionError();
		}
		return uncoveredNodes;
	}

	////

	private void blockExpl(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> node,
			final Expr<BoolType> expr,
			final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats) {
		assert !node.getState().isBottom();

		final ExplState abstractExpl = node.getState().getState().getState3();

		final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(expr, abstractExpl);
		if (simplifiedExpr instanceof BoolLitExpr) {
			assert !((BoolLitExpr) simplifiedExpr).getValue();
			return;
		}

		stats.refineExpl();

		final ExplState concreteExpl = node.getState().getState().getState1();
		final Valuation valI = XtaDataUtils.interpolate(concreteExpl, expr);

		strengthenExpl(node, valI);
		maintainExplCoverage(node, valI, uncoveredNodes);

		if (node.getParent().isPresent()) {
			final ArgEdge<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> inEdge = node
					.getInEdge().get();
			final XtaAction action = inEdge.getAction();
			final Expr<BoolType> newB = XtaDataUtils.pre(Not(valI.toExpr()), action);
			blockExpl(node.getParent().get(), newB, uncoveredNodes, stats);
		}
	}

	private void strengthenExpl(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> node,
			final Valuation interpolant) {
		final XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>> state = node.getState();
		final Prod4State<ExplState, ZoneState, ExplState, ZoneState> prodState = state.getState();
		final ExplState concreteExpl = prodState.getState1();
		final ExplState abstractExpl = prodState.getState3();

		final Collection<Decl<?>> newVars = new HashSet<>();
		newVars.addAll(interpolant.getDecls());
		newVars.addAll(abstractExpl.getDecls());
		final Builder builder = ImmutableValuation.builder();
		for (final Decl<?> decl : newVars) {
			builder.put(decl, concreteExpl.eval(decl).get());
		}
		final Valuation val = builder.build();
		final ExplState newAbstractExpl = ExplState.of(val);

		final Prod4State<ExplState, ZoneState, ExplState, ZoneState> newProdState = prodState.with3(newAbstractExpl);
		final XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	private final void maintainExplCoverage(
			final ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction> node,
			final Valuation interpolant,
			final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes().filter(covered -> !covered.getState().getState().getState3().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	////

	private static Analysis<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ExplState, XtaAction, UnitPrec> concreteExplAnalysis = XtaExplAnalysis.create(system);
		final Analysis<ZoneState, XtaAction, ZonePrec> concreteZoneAnalysis = XtaZoneAnalysis.getInstance();
		final Analysis<ExplState, XtaAction, UnitPrec> abstractExplAnalysis = TopAnalysis.create(ExplState.top(),
				ExplOrd.getInstance());
		final Analysis<ZoneState, XtaAction, UnitPrec> abstractZoneAnalysis = TopAnalysis.create(ZoneState.top(),
				ZoneOrd.getInstance());

		final Prod4Analysis<ExplState, ZoneState, ExplState, ZoneState, XtaAction, UnitPrec, ZonePrec, UnitPrec, UnitPrec> prodAnalysis = Prod4Analysis
				.create(concreteExplAnalysis, concreteZoneAnalysis, abstractExplAnalysis, abstractZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod4Prec<UnitPrec, ZonePrec, UnitPrec, UnitPrec> prec = Prod4Prec.of(unitPrec, zonePrec, unitPrec,
				unitPrec);

		final Analysis<Prod4State<ExplState, ZoneState, ExplState, ZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod4State<ExplState, ZoneState, ExplState, ZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
