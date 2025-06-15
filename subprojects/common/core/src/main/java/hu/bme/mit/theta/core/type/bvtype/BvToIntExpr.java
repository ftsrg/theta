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
package hu.bme.mit.theta.core.type.bvtype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.CastExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;

public final class BvToIntExpr extends CastExpr<BvType, IntType> {

    private static final int HASH_SEED = 9903;
    private static final String OPERATOR_LABEL = "to_int";

    private final boolean signed;

    private BvToIntExpr(final Expr<BvType> op, final boolean signed) {
        super(op);
        this.signed = signed;
    }

    public static BvToIntExpr of(final Expr<BvType> op, final boolean signed) {
        return new BvToIntExpr(op, signed);
    }

    public static BvToIntExpr of(final Expr<BvType> op) {
        return new BvToIntExpr(op, op.getType().getSigned());
    }

    public static BvToIntExpr create(final Expr<?> op, final boolean signed) {
        final Expr<BvType> newOp = castBv(op);
        return BvToIntExpr.of(newOp, signed);
    }

    public static BvToIntExpr create(final Expr<?> op) {
        final Expr<BvType> newOp = castBv(op);
        return create(newOp, newOp.getType().getSigned());
    }

    @Override
    public IntType getType() {
        return Int();
    }

    @Override
    public IntLitExpr eval(final Valuation val) {
        final BvLitExpr opVal = (BvLitExpr) getOp().eval(val);
        if (signed) {
            return IntLitExpr.of(BvUtils.signedBvLitExprToBigInteger(opVal));
        } else {
            return IntLitExpr.of(BvUtils.neutralBvLitExprToBigInteger(opVal));
        }
    }

    @Override
    public BvToIntExpr with(final Expr<BvType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return BvToIntExpr.of(op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final BvToIntExpr that = (BvToIntExpr) obj;
            return this.getOp().equals(that.getOp()) && this.signed == that.signed;
        } else {
            return false;
        }
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public int hashCode() {
        var result = getHashSeed();
        result = 37 * result + getOp().hashCode() + Boolean.hashCode(signed);
        return result;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }

    public boolean isSigned() {
        return signed;
    }

    public BvToIntExpr withSignedness(boolean signed) {
        if (signed == this.signed) return this;
        else return create(getOp(), signed);
    }
}
