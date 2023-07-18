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
package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

import java.util.Collection;

public class ExprInvTransFunc<A extends Action> implements InvTransFunc<BasicExprState, A, UnitPrec> {

    private final ExprActionPre<A> exprActionPre;

    private ExprInvTransFunc(final ExprActionPre<A> exprActionPre) {
        this.exprActionPre = exprActionPre;
    }

    public static <A extends Action> ExprInvTransFunc<A> create(final ExprActionPre<A> exprActionPre) {
        return new ExprInvTransFunc<>(exprActionPre);
    }

    @Override
    public Collection<? extends BasicExprState> getPreStates(BasicExprState state, A action, UnitPrec prec) {
        return ImmutableList.of(BasicExprState.of(exprActionPre.pre(state.toExpr(), action)));
    }
}
