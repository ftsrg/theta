/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public final class AutomaticItpRefToProd2ExplPredPrec implements RefutationToPrec<Prod2Prec<ExplPrec, PredPrec>, ItpRefutation> {

	private final Map<VarDecl<?>, Set<Expr<BoolType>>> atomCount;
	private final ExprSplitter exprSplitter;
	private final AutoExpl autoExpl;

	private AutomaticItpRefToProd2ExplPredPrec(final AutoExpl autoExpl, final ExprSplitter exprSplitter) {
		this.exprSplitter = checkNotNull(exprSplitter);
		this.autoExpl = autoExpl;

		this.atomCount = Containers.createMap();
	}

	public static AutomaticItpRefToProd2ExplPredPrec create(final AutoExpl autoExpl, final ExprSplitter exprSplitter) {
		checkNotNull(autoExpl);
		return new AutomaticItpRefToProd2ExplPredPrec(autoExpl, exprSplitter);
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> toPrec(ItpRefutation refutation, int index) {
		final Expr<BoolType> refExpr = refutation.get(index);
		autoExpl.update(refExpr);

		final var explSelectedVars = ExprUtils.getVars(refExpr).stream()
				.filter(autoExpl::isExpl)
				.collect(Collectors.toSet());
		final var predSelectedExprs = exprSplitter.apply(refExpr).stream()
				.filter(expr -> !ExprUtils.getVars(expr).stream().allMatch(autoExpl::isExpl))
				.collect(Collectors.toSet());

		return Prod2Prec.of(ExplPrec.of(explSelectedVars), PredPrec.of(predSelectedExprs));
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> join(Prod2Prec<ExplPrec, PredPrec> prec1, Prod2Prec<ExplPrec, PredPrec> prec2) {
		final ExplPrec joinedExpl = prec1.getPrec1().join(prec2.getPrec1());
		final PredPrec joinedPred = prec1.getPrec2().join(prec2.getPrec2());
		final var filteredPreds = joinedPred.getPreds().stream()
				.filter(pred -> !joinedExpl.getVars().containsAll(ExprUtils.getVars(pred)))
				.collect(Collectors.toList());
		final PredPrec filteredPred = PredPrec.of(filteredPreds);
		return Prod2Prec.of(joinedExpl, filteredPred);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
