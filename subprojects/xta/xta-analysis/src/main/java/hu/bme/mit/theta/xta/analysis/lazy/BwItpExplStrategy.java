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

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;

import java.util.Collection;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils;
import hu.bme.mit.theta.xta.analysis.expl.itp.ItpExplState;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;

final class BwItpExplStrategy<S extends State> extends ItpExplStrategy<S> {

	public BwItpExplStrategy(final XtaSystem system, final Lens<S, ItpExplState> lens) {
		super(system, lens);
	}

	@Override
	protected Valuation blockExpl(final ArgNode<S, XtaAction> node, final Expr<BoolType> expr,
								  final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		assert !node.getState().isBottom();

		final ExplState abstractExpl = getLens().get(node.getState()).getAbstrState();

		final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(expr, abstractExpl);
		if (simplifiedExpr instanceof BoolLitExpr) {
			assert !((BoolLitExpr) simplifiedExpr).getValue();
			return abstractExpl;
		}

		stats.refineExpl();

		final ExplState concreteExpl = getLens().get(node.getState()).getConcrState();
		final Valuation valI = XtaExplUtils.interpolate(concreteExpl, expr);

		strengthen(node, valI);
		maintainCoverage(node, valI, uncoveredNodes);

		if (node.getParent().isPresent()) {
			final ArgEdge<S, XtaAction> inEdge = node.getInEdge().get();
			final XtaAction action = inEdge.getAction();
			final Expr<BoolType> newB = XtaExplUtils.pre(Not(valI.toExpr()), action);
			blockExpl(node.getParent().get(), newB, uncoveredNodes, stats);
		}

		return valI;
	}

}
