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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.HashSet;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils;
import hu.bme.mit.theta.xta.analysis.expl.itp.ItpExplAnalysis;
import hu.bme.mit.theta.xta.analysis.expl.itp.ItpExplState;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;

abstract class ItpExplStrategy<S extends State> implements AlgorithmStrategy<S, ItpExplState> {

	private final Lens<S, ItpExplState> lens;
	private final Analysis<ItpExplState, XtaAction, UnitPrec> analysis;
	private final Function<ItpExplState, ?> projection;

	public ItpExplStrategy(final XtaSystem system, final Lens<S, ItpExplState> lens) {
		this.lens = checkNotNull(lens);
		analysis = ItpExplAnalysis.create(XtaExplAnalysis.create(system));
		projection = s -> unit();
	}

	@Override
	public final Analysis<ItpExplState, XtaAction, UnitPrec> getAnalysis() {
		return analysis;
	}

	@Override
	public final Function<ItpExplState, ?> getProjection() {
		return projection;
	}

	@Override
	public final boolean mightCover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer) {
		final ExplState covereeExpl = lens.get(coveree.getState()).getConcrState();
		final ExplState covererExpl = lens.get(coverer.getState()).getAbstrState();
		return covereeExpl.isLeq(covererExpl);
	}

	@Override
	public final void cover(final ArgNode<S, XtaAction> coveree, final ArgNode<S, XtaAction> coverer,
							final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		stats.startCloseExplRefinement();
		final ItpExplState covererState = lens.get(coverer.getState());
		blockExpl(coveree, Not(covererState.toExpr()), uncoveredNodes, stats);
		stats.stopCloseExplRefinement();
	}

	@Override
	public final void block(final ArgNode<S, XtaAction> node, final XtaAction action, final S succState,
							final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		assert lens.get(succState).isBottom();
		stats.startExpandExplRefinement();
		final Expr<BoolType> preImage = XtaExplUtils.pre(True(), action);
		blockExpl(node, preImage, uncoveredNodes, stats);
		stats.stopExpandExplRefinement();
	}

	////

	protected abstract Valuation blockExpl(final ArgNode<S, XtaAction> node, final Expr<BoolType> expr,
										   final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats);

	protected final Lens<S, ItpExplState> getLens() {
		return lens;
	}

	protected final void strengthen(final ArgNode<S, XtaAction> node, final Valuation interpolant) {
		final S state = node.getState();
		final ItpExplState itpExplState = lens.get(state);
		final ExplState concreteExpl = itpExplState.getConcrState();
		final ExplState abstractExpl = itpExplState.getAbstrState();

		final Collection<Decl<?>> newVars = new HashSet<>();
		newVars.addAll(interpolant.getDecls());
		newVars.addAll(abstractExpl.getDecls());
		final ImmutableValuation.Builder builder = ImmutableValuation.builder();
		for (final Decl<?> decl : newVars) {
			builder.put(decl, concreteExpl.eval(decl).get());
		}
		final Valuation val = builder.build();
		final ExplState newAbstractExpl = ExplState.of(val);

		final ItpExplState newItpExplState = itpExplState.withAbstrState(newAbstractExpl);
		final S newState = lens.set(state, newItpExplState);
		node.setState(newState);
	}

	protected final void maintainCoverage(final ArgNode<S, XtaAction> node, final Valuation interpolant,
										  final Collection<ArgNode<S, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<S, XtaAction>> uncovered = node.getCoveredNodes()
				.filter(covered -> shouldUncover(covered, interpolant)).collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}

	private boolean shouldUncover(final ArgNode<S, XtaAction> covered, final Valuation interpolant) {
		final ItpExplState coveredExpl = lens.get(covered.getState());
		return !coveredExpl.getAbstrState().isLeq(interpolant);
	}

}