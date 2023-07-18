/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Interpolator;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprSimplifier;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.SimplifierLevel;

import java.util.Collection;
import java.util.Collections;

import static java.util.stream.Collectors.toList;

public final class ExplExprInterpolator implements Interpolator<ExplState, BasicExprState> {

    private static final ExprSimplifier exprSimplifier = ExprSimplifier.create(SimplifierLevel.LITERAL_ONLY);
    private static final ExplExprInterpolator INSTANCE = new ExplExprInterpolator();

    private ExplExprInterpolator() {
    }

    public static ExplExprInterpolator getInstance() {
        return INSTANCE;
    }

    @Override
    public BasicExprState toItpDom(final ExplState explState) {
        return BasicExprState.of(explState.toExpr());
    }

    @Override
    public ExplState interpolate(final ExplState explState, final BasicExprState exprState) {
        final Valuation valA = explState;
        final Expr<BoolType> exprB = exprState.toExpr();
        final Collection<VarDecl<?>> vars = ExprUtils.getVars(exprB).stream().filter(valA.getDecls()::contains).collect(toList());
        final MutableValuation valI = new MutableValuation();
        for (final VarDecl<?> var : vars) {
            final LitExpr<?> val = valA.eval(var).get();
            valI.put(var, val);
        }
        assert refutes(valI, exprB);

        for (final VarDecl<?> var : vars) {
            valI.remove(var);
            if (!refutes(valI, exprB)) {
                final LitExpr<?> val = valA.eval(var).get();
                valI.put(var, val);
            }
        }
        return ExplState.of(valI);
    }

    @Override
    public Collection<BasicExprState> complement(final BasicExprState exprState) {
        final Expr<BoolType> complementExpr = BoolExprs.Not(exprState.toExpr());
        return Collections.singleton(BasicExprState.of(complementExpr));
    }

    @Override
    public boolean refutes(final ExplState explState, final BasicExprState exprState) {
        return refutes(explState, exprState.toExpr());
    }

    private boolean refutes(final Valuation val, final Expr<BoolType> expr) {
        final Expr<BoolType> simplifiedExpr = exprSimplifier.simplify(expr, val);
        return simplifiedExpr.equals(BoolExprs.False());
    }
}
