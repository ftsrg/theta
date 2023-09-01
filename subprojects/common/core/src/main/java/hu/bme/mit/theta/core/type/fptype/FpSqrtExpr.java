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
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.utils.FpUtils;
import org.kframework.mpfr.BigFloat;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

public class FpSqrtExpr extends UnaryExpr<FpType, FpType> {

    private static final int HASH_SEED = 6669;
    private static final String OPERATOR_LABEL = "fpsqrt";

    private final FpRoundingMode roundingMode;

    private FpSqrtExpr(final FpRoundingMode roundingMode, final Expr<FpType> op) {
        super(op);
        checkNotNull(roundingMode);
        this.roundingMode = roundingMode;
    }

    public static FpSqrtExpr of(final FpRoundingMode roundingMode, final Expr<FpType> op) {
        return new FpSqrtExpr(roundingMode, castFp(op));
    }

    public static FpSqrtExpr create(final FpRoundingMode roundingMode, final Expr<?> op) {
        checkNotNull(op);
        return FpSqrtExpr.of(roundingMode, castFp(op));
    }

    public FpRoundingMode getRoundingMode() {
        return roundingMode;
    }

    @Override
    public FpType getType() {
        return getOp().getType();
    }

    @Override
    public LitExpr<FpType> eval(Valuation val) {
        final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
        BigFloat sqrt = FpUtils.fpLitExprToBigFloat(roundingMode, opVal)
                .sqrt(FpUtils.getMathContext(getType(), roundingMode));
        return FpUtils.bigFloatToFpLitExpr(sqrt, getType());
    }

    @Override
    public UnaryExpr<FpType, FpType> with(Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpSqrtExpr.of(roundingMode, op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpSqrtExpr that = (FpSqrtExpr) obj;
            return this.getOp().equals(that.getOp()) && roundingMode.equals(that.roundingMode);
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
 
