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

import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.HashSet;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.ImmutableValuation.Builder;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.expl.itp.ItpExplState;

abstract class ItpExplRefiner {

	public abstract <S extends State> Valuation blockExpl(
			final ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction> node, final Expr<BoolType> expr,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats);

	protected final <S extends State> void strengthen(
			final ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction> node, final Valuation interpolant) {
		final XtaState<Prod2State<ItpExplState, S>> state = node.getState();
		final Prod2State<ItpExplState, S> prodState = state.getState();
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
		final Prod2State<ItpExplState, S> newProdState = prodState.with1(newItpExplState);
		final XtaState<Prod2State<ItpExplState, S>> newState = state.withState(newProdState);
		node.setState(newState);
	}

	protected final <S extends State> void maintainCoverage(
			final ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction> node, final Valuation interpolant,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction>> uncoveredNodes) {
		final Collection<ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction>> uncovered = node.getCoveredNodes()
				.filter(covered -> !covered.getState().getState().getState1().getAbstrState().isLeq(interpolant))
				.collect(toList());
		uncoveredNodes.addAll(uncovered);
		uncovered.forEach(ArgNode::unsetCoveringNode);
	}
}
