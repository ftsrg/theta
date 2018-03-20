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
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils;
import hu.bme.mit.theta.xta.analysis.expl.itp.ItpExplState;

final class BwItpExplRefiner extends ItpExplRefiner {

	private BwItpExplRefiner() {
	}

	private static class LazyHolder {
		static final BwItpExplRefiner INSTANCE = new BwItpExplRefiner();
	}

	public static BwItpExplRefiner getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public <S extends State> void blockExpl(final ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction> node,
			final Expr<BoolType> expr,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction>> uncoveredNodes,
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
		final Valuation valI = XtaExplUtils.interpolate(concreteExpl, expr);

		strengthen(node, valI);
		maintainCoverage(node, valI, uncoveredNodes);

		if (node.getParent().isPresent()) {
			final ArgEdge<XtaState<Prod2State<ItpExplState, S>>, XtaAction> inEdge = node.getInEdge().get();
			final XtaAction action = inEdge.getAction();
			final Expr<BoolType> newB = XtaExplUtils.pre(Not(valI.toExpr()), action);
			blockExpl(node.getParent().get(), newB, uncoveredNodes, stats);
		}
	}

}
