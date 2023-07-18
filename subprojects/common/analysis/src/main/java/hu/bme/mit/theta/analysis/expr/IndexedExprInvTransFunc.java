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

import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import java.util.Collection;
import java.util.Collections;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class IndexedExprInvTransFunc implements InvTransFunc<IndexedExprState, ExprAction, UnitPrec> {

    private final static IndexedExprInvTransFunc INSTANCE = new IndexedExprInvTransFunc();

    private IndexedExprInvTransFunc() {
    }

    public static IndexedExprInvTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends IndexedExprState> getPreStates(IndexedExprState state, ExprAction action, UnitPrec prec) {
        final VarIndexing currentIndexing = state.getVarIndexing();
        final Expr<BoolType> preExpr = And(state.toExpr(), PathUtils.unfoldReverse(action.toExpr(), currentIndexing));
        final VarIndexing newIndexing = currentIndexing.add(action.nextIndexing());
        final IndexedExprState preState = IndexedExprState.of(preExpr, newIndexing);
        return Collections.singleton(preState);
    }
}
