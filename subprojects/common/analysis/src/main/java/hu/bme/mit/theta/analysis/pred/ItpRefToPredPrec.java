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
package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Collection;

/** Transformer from interpolant refutation to predicate precision. */
public class ItpRefToPredPrec implements RefutationToPrec<PredPrec, ItpRefutation> {

    private final ExprSplitter exprSplitter;

    public ItpRefToPredPrec(final ExprSplitter exprSplitter) {
        this.exprSplitter = checkNotNull(exprSplitter);
    }

    @Override
    public PredPrec toPrec(final ItpRefutation refutation, final int index) {
        final Expr<BoolType> expr = refutation.get(index);
        final Collection<Expr<BoolType>> exprs = exprSplitter.apply(expr);
        final PredPrec prec = PredPrec.of(exprs);
        return prec;
    }

    @Override
    public PredPrec join(final PredPrec prec1, final PredPrec prec2) {
        checkNotNull(prec1);
        checkNotNull(prec2);
        return prec1.join(prec2);
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName())
                .aligned()
                .add(exprSplitter)
                .toString();
    }
}
