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
package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Sign and significand is presumed to be unsigned Exponent is presumed to be signed
 */
public class FpToBvExpr extends UnaryExpr<FpType, BvType> {

    private static final int HASH_SEED = 6796;
    private static final String OPERATOR_LABEL = "fptobv";

    private final Expr<FpType> op;
    private final int size;
    private final boolean sgn;

    private final FpRoundingMode roundingMode;

    private FpToBvExpr(final FpRoundingMode roundingMode, final Expr<FpType> op, final int size,
                       final boolean sgn) {
        super(op);
        checkNotNull(op);
        this.op = op;

        this.size = size;
        this.sgn = sgn;

        checkNotNull(roundingMode);
        this.roundingMode = roundingMode;
    }

    public static FpToBvExpr of(final FpRoundingMode roundingMode, final Expr<FpType> op,
                                final int size, final boolean sgn) {
        return new FpToBvExpr(roundingMode, op, size, sgn);
    }

    public static FpToBvExpr create(final FpRoundingMode roundingMode, final Expr<FpType> op,
                                    final int size, final boolean sgn) {
        return FpToBvExpr.of(roundingMode, op, size, sgn);
    }

    public int getSize() {
        return size;
    }

    public boolean getSgn() {
        return sgn;
    }

    @Override
    public FpToBvExpr with(Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpToBvExpr.of(roundingMode, op, size, sgn);
        }
    }

    @Override
    public BvType getType() {
        return BvType.of(size);
    }

    @Override
    public BvLitExpr eval(Valuation val) {
        final FpLitExpr op = (FpLitExpr) this.op.eval(val);

        BigInteger bigIntegerValue = FpUtils.fpLitExprToBigFloat(roundingMode, op).toBigInteger();
        if (sgn) {
            return BvUtils.bigIntegerToSignedBvLitExpr(bigIntegerValue, size);
        } else {
            return BvUtils.bigIntegerToUnsignedBvLitExpr(bigIntegerValue, size);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpToBvExpr that = (FpToBvExpr) obj;
            return this.getOp().equals(that.getOp()) && size == that.size && sgn == that.sgn
                    && roundingMode.equals(that.roundingMode);
        } else {
            return false;
        }
    }

    protected int getHashSeed() {
        return HASH_SEED;
    }

    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }

    public FpRoundingMode getRoundingMode() {
        return roundingMode;
    }
}
 
