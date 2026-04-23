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
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.CastExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;

public final class IntToBvExpr extends CastExpr<IntType, BvType> {

    private static final int HASH_SEED = 9941;
    private static final String OPERATOR_LABEL = "to_bv";

    private final BvType type;

    private IntToBvExpr(final Expr<IntType> op, final BvType type) {
        super(op);
        this.type = type;
    }

    public static IntToBvExpr of(final Expr<IntType> op, final BvType type) {
        return new IntToBvExpr(op, type);
    }

    public static IntToBvExpr create(final Expr<?> op, final BvType type) {
        return IntToBvExpr.of(cast(op, Int()), type);
    }

    @Override
    public BvType getType() {
        return type;
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        final IntLitExpr opVal = (IntLitExpr) getOp().eval(val);
        if (type.getSigned()) {
            return BvUtils.bigIntegerToSignedBvLitExpr(opVal.getValue(), type.getSize());
        } else if (type.equals(BvType.of(type.getSize(), false))) {
            return BvUtils.bigIntegerToUnsignedBvLitExpr(opVal.getValue(), type.getSize());
        } else {
            return BvUtils.bigIntegerToNeutralBvLitExpr(opVal.getValue(), type.getSize());
        }
    }

    @Override
    public IntToBvExpr with(final Expr<IntType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return IntToBvExpr.of(op, type);
        }
    }

    public IntToBvExpr withType(final BvType type) {
        if (this.type.equals(type)) {
            return this;
        } else {
            return IntToBvExpr.of(getOp(), type);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final IntToBvExpr that = (IntToBvExpr) obj;
            return this.getOp().equals(that.getOp()) && this.type.equals(that.type);
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
        result = 37 * result + getOp().hashCode() + type.hashCode();
        return result;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }
}
