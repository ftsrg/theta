/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import java.util.Collection;
import java.util.Collections;

public class LazyExprTransFunc<A extends Action> implements TransFunc<BasicExprState, A, UnitPrec> {

    private final ExprPost<A> exprPost;

    private LazyExprTransFunc(final ExprPost<A> exprPost) {
        this.exprPost = exprPost;
    }

    public static <A extends Action> LazyExprTransFunc<A> create(final ExprPost<A> exprPost) {
        return new LazyExprTransFunc<>(exprPost);
    }

    @Override
    public Collection<? extends BasicExprState> getSuccStates(
            final BasicExprState state, final A action, final UnitPrec prec) {
        return Collections.singleton(exprPost.post(state, action));
    }
}
