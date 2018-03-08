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
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
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
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.ImmutableValuation.Builder;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
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

public abstract class ExplItpStrategy implements AlgorithmStrategy<Prod2State<ItpExplState, ItpZoneState>> {

	private final Analysis<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction, UnitPrec> analysis;
	private final ZonePrec prec;

	protected ExplItpStrategy(final XtaSystem system) {
		checkNotNull(system);
		analysis = createAnalysis(system);
		prec = ZonePrec.of(system.getClockVars());
	}

	protected abstract ZoneState blockZone(
			final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> node, final ZoneState zone,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats);

	////

	protected final ZoneState pre(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.pre(state, action, prec);
	}

	protected final ZoneState post(final ZoneState state, final XtaAction action) {
		return XtaZoneUtils.post(state, action, prec);
	}

	protected final void strengthenZone(final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> node,
			final ZoneState interpolant) {
		final XtaState<Prod2State<ItpExplState, ItpZoneState>> state = node.getState();
		final Prod2State<ItpExplState, ItpZoneState> prodState = state.getState();
		final ItpZoneState itpZoneState = prodState.getState2();
		final ZoneState abstrZoneState = itpZoneState.getAbstrState();

		final ZoneState newAbstrZoneState = ZoneState.intersection(abstrZoneState, interpolant);

		final ItpZoneState newItpZoneState = itpZoneState.withAbstrState(newAbstrZoneState);
		final Prod2State<ItpExplState, ItpZoneState> newProdState = prodState.with2(newItpZoneState);
		final XtaState<Prod2State<ItpExplState, ItpZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	protected final void maintainZoneCoverage(
			final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> node,
			final ZoneState interpolant,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes()
				.filter(covered -> !covered.getState().getState().getState2().getAbstrState().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	////

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
		blockExpl(coveree, Not(coverer.getState().getState().getState1().toExpr()), uncoveredNodes, stats);
		stats.stopCloseExplRefinement();

		stats.startCloseZoneRefinement();
		final Collection<ZoneState> complementZones = coverer.getState().getState().getState2().getAbstrState()
				.complement();
		for (final ZoneState complementZone : complementZones) {
			blockZone(coveree, complementZone, uncoveredNodes, stats);
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

	private void blockExpl(final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> node,
			final Expr<BoolType> expr,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats) {
		assert !node.getState().isBottom();

		final ExplState abstractExpl = node.getState().getState().getState1().getAbstrState();

		final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(expr, abstractExpl);
		if (simplifiedExpr instanceof BoolLitExpr) {
			assert !((BoolLitExpr) simplifiedExpr).getValue();
			return;
		}

		stats.refineExpl();

		final ExplState concreteExpl = node.getState().getState().getState1().getConcrState();
		final Valuation valI = XtaDataUtils.interpolate(concreteExpl, expr);

		strengthenExpl(node, valI);
		maintainExplCoverage(node, valI, uncoveredNodes);

		if (node.getParent().isPresent()) {
			final ArgEdge<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> inEdge = node.getInEdge().get();
			final XtaAction action = inEdge.getAction();
			final Expr<BoolType> newB = XtaDataUtils.pre(Not(valI.toExpr()), action);
			blockExpl(node.getParent().get(), newB, uncoveredNodes, stats);
		}
	}

	private void strengthenExpl(final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> node,
			final Valuation interpolant) {
		final XtaState<Prod2State<ItpExplState, ItpZoneState>> state = node.getState();
		final Prod2State<ItpExplState, ItpZoneState> prodState = state.getState();
		final ItpExplState itpExplState = prodState.getState1();
		final ExplState concreteExpl = itpExplState.getConcrState();
		final ExplState abstractExpl = itpExplState.getAbstrState();

		final Collection<Decl<?>> newVars = new HashSet<>();
		newVars.addAll(interpolant.getDecls());
		newVars.addAll(abstractExpl.getDecls());
		final Builder builder = ImmutableValuation.builder();
		for (final Decl<?> decl : newVars) {
			builder.put(decl, concreteExpl.eval(decl).get());
		}
		final Valuation val = builder.build();
		final ExplState newAbstractExpl = ExplState.of(val);

		final ItpExplState newItpExplState = itpExplState.withAbstrState(newAbstractExpl);
		final Prod2State<ItpExplState, ItpZoneState> newProdState = prodState.with1(newItpExplState);
		final XtaState<Prod2State<ItpExplState, ItpZoneState>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	private final void maintainExplCoverage(
			final ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction> node,
			final Valuation interpolant,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<ItpExplState, ItpZoneState>>, XtaAction>> uncovered = node
				.getCoveredNodes()
				.filter(covered -> !covered.getState().getState().getState1().getAbstrState().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
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
