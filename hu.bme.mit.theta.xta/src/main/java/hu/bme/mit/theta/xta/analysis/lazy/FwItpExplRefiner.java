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

final class FwItpExplRefiner extends ItpExplRefiner {

	private FwItpExplRefiner() {
	}

	private static class LazyHolder {
		static final FwItpExplRefiner INSTANCE = new FwItpExplRefiner();
	}

	public static FwItpExplRefiner getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public <S extends State> Valuation blockExpl(final ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction> node,
			final Expr<BoolType> expr,
			final Collection<ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats) {

		final ExplState abstrState = node.getState().getState().getState1().getAbstrState();

		final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(expr, abstrState);
		if (simplifiedExpr instanceof BoolLitExpr) {
			assert !((BoolLitExpr) simplifiedExpr).getValue();
			return abstrState;
		}

		stats.refineExpl();
		if (node.getInEdge().isPresent()) {
			final ArgEdge<XtaState<Prod2State<ItpExplState, S>>, XtaAction> inEdge = node.getInEdge().get();
			final XtaAction action = inEdge.getAction();
			final ArgNode<XtaState<Prod2State<ItpExplState, S>>, XtaAction> parent = inEdge.getSource();

			final Expr<BoolType> B_pre = XtaExplUtils.pre(expr, action);
			final Valuation A_pre = blockExpl(parent, B_pre, uncoveredNodes, stats);

			final Expr<BoolType> B = expr;
			final Valuation A = XtaExplUtils.post(A_pre, action);

			final Valuation interpolant = XtaExplUtils.interpolate(A, B);

			strengthen(node, interpolant);
			maintainCoverage(node, interpolant, uncoveredNodes);

			return interpolant;
		} else {
			final ExplState concrState = node.getState().getState().getState1().getConcrState();

			final Valuation interpolant = XtaExplUtils.interpolate(concrState, expr);

			strengthen(node, interpolant);
			maintainCoverage(node, interpolant, uncoveredNodes);

			return interpolant;
		}
	}

}
