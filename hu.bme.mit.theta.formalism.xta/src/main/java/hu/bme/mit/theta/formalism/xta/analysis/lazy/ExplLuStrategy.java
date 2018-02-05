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
import hu.bme.mit.theta.analysis.prod3.Prod3Analysis;
import hu.bme.mit.theta.analysis.prod3.Prod3Prec;
import hu.bme.mit.theta.analysis.prod3.Prod3State;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneState;
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
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaLuZoneUtils;
import hu.bme.mit.theta.formalism.xta.analysis.zone.XtaZoneAnalysis;

public final class ExplLuStrategy implements AlgorithmStrategy<Prod3State<ExplState, ExplState, LuZoneState>> {

	private final Analysis<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction, UnitPrec> analysis;

	private ExplLuStrategy(final XtaSystem system) {
		checkNotNull(system);
		analysis = createAnalysis(system);
	}

	public static ExplLuStrategy create(final XtaSystem system) {
		return new ExplLuStrategy(system);
	}

	@Override
	public Analysis<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public Partition<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>, ?> createReachedSet() {
		final Partition<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>, List<Loc>> partition = Partition
				.of(n -> n.getState().getLocs());
		return partition;
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> coverer) {
		final ExplState covereeExpl = coveree.getState().getState().getState1();
		final ExplState covererExpl = coverer.getState().getState().getState2();
		final ZoneState covereeZone = coveree.getState().getState().getState3().getZone();
		final ZoneState covererZone = coverer.getState().getState().getState3().getZone();
		final BoundFunc covererBoundFunc = coverer.getState().getState().getState3().getBoundFunction();
		return covereeExpl.isLeq(covererExpl) && covereeZone.isLeq(covererZone, covererBoundFunc);
	}

	@Override
	public boolean shouldExclude(final XtaState<Prod3State<ExplState, ExplState, LuZoneState>> state) {
		return state.getState().isBottom1() || state.getState().isBottom3();
	}

	@Override
	public Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> forceCover(
			final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> coveree,
			final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> coverer,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();

		stats.startCloseExplRefinement();
		blockExpl(coveree, Not(coverer.getState().getState().getState2().toExpr()), uncoveredNodes, stats);
		stats.stopCloseExplRefinement();

		stats.startCloseZoneRefinement();
		final BoundFunc boundFunc = coverer.getState().getState().getState3().getBoundFunction();
		propagateBounds(coveree, boundFunc, uncoveredNodes, stats);
		stats.stopCloseZoneRefinement();

		return uncoveredNodes;
	}

	@Override
	public Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> block(
			final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> node,
			final XtaAction action, final XtaState<Prod3State<ExplState, ExplState, LuZoneState>> succState,
			final LazyXtaStatistics.Builder stats) {
		final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncoveredNodes = new ArrayList<>();
		if (succState.getState().isBottom1()) {
			stats.startExpandExplRefinement();
			final Expr<BoolType> preImage = XtaDataUtils.pre(True(), action);
			blockExpl(node, preImage, uncoveredNodes, stats);
			stats.stopExpandExplRefinement();
		} else if (succState.getState().isBottom3()) {
			stats.startExpandZoneRefinement();
			final BoundFunc preImage = XtaLuZoneUtils.pre(BoundFunc.top(), action);
			propagateBounds(node, preImage, uncoveredNodes, stats);
			stats.stopExpandZoneRefinement();
		} else {
			throw new AssertionError();
		}
		return uncoveredNodes;
	}

	////

	private final void blockExpl(final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> node,
			final Expr<BoolType> expr,
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats) {
		assert !node.getState().isBottom();

		final ExplState abstractExpl = node.getState().getState().getState2();

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
			final ArgEdge<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> inEdge = node.getInEdge()
					.get();
			final XtaAction action = inEdge.getAction();
			final Expr<BoolType> newB = XtaDataUtils.pre(Not(valI.toExpr()), action);
			blockExpl(node.getParent().get(), newB, uncoveredNodes, stats);
		}
	}

	private void propagateBounds(final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> node,
			final BoundFunc boundFunction,
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats) {
		final BoundFunc oldBoundFunction = node.getState().getState().getState3().getBoundFunction();
		if (!boundFunction.isLeq(oldBoundFunction)) {
			stats.refineZone();

			strengthenZone(node, boundFunction);
			maintainZoneCoverage(node, boundFunction, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> inEdge = node
						.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> parent = inEdge
						.getSource();
				final BoundFunc preBound = XtaLuZoneUtils.pre(boundFunction, action);
				propagateBounds(parent, preBound, uncoveredNodes, stats);
			}
		}
	}

	private void strengthenExpl(final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> node,
			final Valuation interpolant) {
		final XtaState<Prod3State<ExplState, ExplState, LuZoneState>> state = node.getState();
		final Prod3State<ExplState, ExplState, LuZoneState> prodState = state.getState();
		final ExplState concreteExpl = prodState.getState1();
		final ExplState abstractExpl = prodState.getState2();

		final Collection<Decl<?>> newVars = new HashSet<>();
		newVars.addAll(interpolant.getDecls());
		newVars.addAll(abstractExpl.getDecls());
		final Builder builder = ImmutableValuation.builder();
		for (final Decl<?> decl : newVars) {
			builder.put(decl, concreteExpl.eval(decl).get());
		}
		final Valuation val = builder.build();
		final ExplState newAbstractExpl = ExplState.of(val);

		final Prod3State<ExplState, ExplState, LuZoneState> newProdState = prodState.with2(newAbstractExpl);
		final XtaState<Prod3State<ExplState, ExplState, LuZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	private void strengthenZone(final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> node,
			final BoundFunc interpolant) {
		final XtaState<Prod3State<ExplState, ExplState, LuZoneState>> state = node.getState();
		final Prod3State<ExplState, ExplState, LuZoneState> prodState = state.getState();
		final LuZoneState luZoneState = prodState.getState3();
		final BoundFunc oldBoundFunction = luZoneState.getBoundFunction();

		final BoundFunc newBoundFunction = oldBoundFunction.merge(interpolant);

		final LuZoneState newLuZoneState = luZoneState.withBoundFunction(newBoundFunction);
		final Prod3State<ExplState, ExplState, LuZoneState> newProdState = prodState.with3(newLuZoneState);
		final XtaState<Prod3State<ExplState, ExplState, LuZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	private final void maintainExplCoverage(
			final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> node,
			final Valuation interpolant,
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes().filter(covered -> !covered.getState().getState().getState2().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	private final void maintainZoneCoverage(
			final ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction> node,
			final BoundFunc interpolant,
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes().filter(covered -> !covered.getState().getState().getState3().getZone()
						.isLeq(node.getState().getState().getState3().getZone(), interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	////

	private static Analysis<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction, UnitPrec> createAnalysis(
			final XtaSystem system) {
		final Analysis<ExplState, XtaAction, UnitPrec> concreteExplAnalysis = XtaExplAnalysis.create(system);
		final Analysis<ExplState, XtaAction, UnitPrec> abstractExplAnalysis = TopAnalysis.create(ExplState.top(),
				ExplOrd.getInstance());
		final Analysis<LuZoneState, XtaAction, ZonePrec> luZoneAnalysis = LuZoneAnalysis
				.create(XtaZoneAnalysis.getInstance());

		final Prod3Analysis<ExplState, ExplState, LuZoneState, XtaAction, UnitPrec, UnitPrec, ZonePrec> prodAnalysis = Prod3Analysis
				.create(concreteExplAnalysis, abstractExplAnalysis, luZoneAnalysis);

		final UnitPrec unitPrec = UnitPrec.getInstance();
		final ZonePrec zonePrec = ZonePrec.of(system.getClockVars());
		final Prod3Prec<UnitPrec, UnitPrec, ZonePrec> prec = Prod3Prec.of(unitPrec, unitPrec, zonePrec);

		final Analysis<Prod3State<ExplState, ExplState, LuZoneState>, XtaAction, UnitPrec> mappingAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, u -> prec);
		final Analysis<XtaState<Prod3State<ExplState, ExplState, LuZoneState>>, XtaAction, UnitPrec> analysis = XtaAnalysis
				.create(system, mappingAnalysis);
		return analysis;
	}

}
