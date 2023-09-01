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
package hu.bme.mit.theta.core.type.rattype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class RatToIntExpr extends UnaryExpr<RatType, IntType> {

    private static final int HASH_SEED = 4828;
    private static final String OPERATOR_LABEL = "to_int";

    private RatToIntExpr(final Expr<RatType> op) {
        super(op);
    }

    public static RatToIntExpr of(final Expr<RatType> op) {
        return new RatToIntExpr(op);
    }

    public static RatToIntExpr create(final Expr<?> op) {
        final Expr<RatType> newOp = cast(op, Rat());
        return RatToIntExpr.of(newOp);
    }

    @Override
    public IntType getType() {
        return Int();
    }

    @Override
    public IntLitExpr eval(final Valuation val) {
        final RatLitExpr opVal = (RatLitExpr) getOp().eval(val);
        return opVal.toInt();
    }

    @Override
    public RatToIntExpr with(final Expr<RatType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return RatToIntExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final RatToIntExpr that = (RatToIntExpr) obj;
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
