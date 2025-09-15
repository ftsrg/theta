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
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.CastExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class IntToRatExpr extends CastExpr<IntType, RatType> {

    private static final int HASH_SEED = 1627;
    private static final String OPERATOR_LABEL = "to_rat";

    private IntToRatExpr(final Expr<IntType> op) {
        super(op);
    }

    public static IntToRatExpr of(final Expr<IntType> op) {
        return new IntToRatExpr(op);
    }

    public static IntToRatExpr create(final Expr<?> op) {
        final Expr<IntType> newOp = cast(op, Int());
        return IntToRatExpr.of(newOp);
    }

    @Override
    public RatType getType() {
        return Rat();
    }

    @Override
    public RatLitExpr eval(final Valuation val) {
        final IntLitExpr opVal = (IntLitExpr) getOp().eval(val);
        return opVal.toRat();
    }

    @Override
    public IntToRatExpr with(final Expr<IntType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return IntToRatExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final IntToRatExpr that = (IntToRatExpr) obj;
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
