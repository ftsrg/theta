/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import java.util.Collection;
import java.util.Set;

public final class ItpRefToProd2ExplPredPrec
        implements RefutationToPrec<Prod2Prec<ExplPrec, PredPrec>, ItpRefutation> {

    private final Set<VarDecl<?>> explPreferredVars;
    private final ExprSplitter exprSplitter;

    private ItpRefToProd2ExplPredPrec(
            final Set<VarDecl<?>> explPreferredVars, final ExprSplitter exprSplitter) {
        this.explPreferredVars = checkNotNull(explPreferredVars);
        this.exprSplitter = checkNotNull(exprSplitter);
    }

    public static ItpRefToProd2ExplPredPrec create(
            final Set<VarDecl<?>> explPreferredVars, final ExprSplitter exprSplitter) {
        return new ItpRefToProd2ExplPredPrec(explPreferredVars, exprSplitter);
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> toPrec(ItpRefutation refutation, int index) {
        final Collection<Expr<BoolType>> exprs = exprSplitter.apply(refutation.get(index));
        Set<VarDecl<?>> explSelectedVars = Containers.createSet();
        Set<Expr<BoolType>> predSelectedExprs = Containers.createSet();
        for (var expr : exprs) {
            final Set<VarDecl<?>> containedVars = ExprUtils.getVars(expr);
            boolean allExpl = true;
            for (var decl : containedVars) {
                if (explPreferredVars.contains(decl)) {
                    explSelectedVars.add(decl);
                } else {
                    allExpl = false;
                }
            }
            if (!allExpl) {
                predSelectedExprs.add(expr);
            }
        }
        return Prod2Prec.of(ExplPrec.of(explSelectedVars), PredPrec.of(predSelectedExprs));
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> join(
            Prod2Prec<ExplPrec, PredPrec> prec1, Prod2Prec<ExplPrec, PredPrec> prec2) {
        return Prod2Prec.of(
                prec1.getPrec1().join(prec2.getPrec1()), prec1.getPrec2().join(prec2.getPrec2()));
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }
}
