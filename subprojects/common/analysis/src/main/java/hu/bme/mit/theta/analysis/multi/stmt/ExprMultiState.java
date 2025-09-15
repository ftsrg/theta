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
package hu.bme.mit.theta.analysis.multi.stmt;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.multi.MultiSide;
import hu.bme.mit.theta.analysis.multi.MultiState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ExprMultiState<L extends ExprState, R extends ExprState, D extends ExprState>
        extends MultiState<L, R, D> implements ExprState {

    private ExprMultiState(
            L ls, R rs, D data, MultiSide sourceSide, boolean sourceMattersInEquality) {
        super(ls, rs, data, sourceSide, sourceMattersInEquality);
    }

    public static <L extends ExprState, R extends ExprState, D extends ExprState>
            ExprMultiState<L, R, D> create(
                    L ls, R rs, D d, MultiSide sourceSide, boolean sourceMattersInEquality) {
        return new ExprMultiState<>(ls, rs, d, sourceSide, sourceMattersInEquality);
    }

    public static <L extends ExprState, R extends ExprState, D extends ExprState>
            ExprMultiState<L, R, D> create(L ls, R rs, D d, MultiSide sourceSide) {
        return create(ls, rs, d, sourceSide, true);
    }

    public static <L extends ExprState, R extends ExprState, D extends ExprState>
            ExprMultiState<L, R, D> createInitial(
                    L ls, R rs, D d, boolean sourceMattersInEquality) {
        return create(ls, rs, d, null, sourceMattersInEquality);
    }

    public static <L extends ExprState, R extends ExprState, D extends ExprState>
            ExprMultiState<L, R, D> createInitial(L ls, R rs, D d) {
        return createInitial(ls, rs, d, true);
    }

    @Override
    public Expr<BoolType> toExpr() {
        return And(And(getLeftState().toExpr(), getRightState().toExpr()), getDataState().toExpr());
    }
}
