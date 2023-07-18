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
package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import java.util.Collection;
import java.util.Collections;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class IndexedExprTransFunc implements TransFunc<IndexedExprState, ExprAction, UnitPrec> {

    private final static IndexedExprTransFunc INSTANCE = new IndexedExprTransFunc();

    private IndexedExprTransFunc() {
    }

    public static IndexedExprTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends IndexedExprState> getSuccStates(IndexedExprState state, ExprAction action, UnitPrec prec) {
        final VarIndexing currentIndexing = state.getVarIndexing();
        final Expr<BoolType> succExpr = And(state.toExpr(), PathUtils.unfold(action.toExpr(), currentIndexing));
        final VarIndexing newIndexing = currentIndexing.add(action.nextIndexing());
        final IndexedExprState succState = IndexedExprState.of(succExpr, newIndexing);
        return Collections.singleton(succState);
    }
}
