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
package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;

public final class IntNegExpr extends NegExpr<IntType> {

    private static final int HASH_SEED = 3359;
    private static final String OPERATOR_LABEL = "-";

    private IntNegExpr(final Expr<IntType> op) {
        super(op);
    }

    public static IntNegExpr of(final Expr<IntType> op) {
        return new IntNegExpr(op);
    }

    public static IntNegExpr create(final Expr<?> op) {
        final Expr<IntType> newOp = cast(op, Int());
        return IntNegExpr.of(newOp);
    }

    @Override
    public IntType getType() {
        return Int();
    }

    @Override
    public IntLitExpr eval(final Valuation val) {
        final IntLitExpr opVal = (IntLitExpr) getOp().eval(val);
        return opVal.neg();
    }

    @Override
    public IntNegExpr with(final Expr<IntType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return IntNegExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final IntNegExpr that = (IntNegExpr) obj;
            return this.getOp().equals(that.getOp());
        } else {
            return false;
        }
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }
}
