/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;

/**
 * A floating-point value read out of a raw IEEE-754 bit pattern -- the inverse of {@link
 * FpToIeeeBvExpr}, a reinterpretation rather than a numeric conversion. {@code 0x3FF0000000000000}
 * becomes {@code 1.0}, not the float nearest to the integer {@code 0x3FF0000000000000}. This is the
 * read side of {@code union { double value; uint64_t bits; }}: writing {@code bits} and reading
 * {@code value}.
 *
 * <p>The bitvector's width must match the target format ({@code exponent + significand + 1}), so
 * unlike {@link FpFromBvExpr} there is no rounding mode and no signedness.
 */
public class FpFromIeeeBvExpr extends UnaryExpr<BvType, FpType> {

    private static final int HASH_SEED = 6829;
    private static final String OPERATOR_LABEL = "fpfromieeebv";

    private final FpType fpType;

    private FpFromIeeeBvExpr(final Expr<BvType> op, final FpType fpType) {
        super(op);
        this.fpType = checkNotNull(fpType);
    }

    public static FpFromIeeeBvExpr of(final Expr<BvType> op, final FpType fpType) {
        checkArgument(
                op.getType().getSize() == FpToIeeeBvExpr.bitWidth(fpType),
                "The bitvector width must equal the float's encoded width");
        return new FpFromIeeeBvExpr(op, fpType);
    }

    public static FpFromIeeeBvExpr create(final Expr<BvType> op, final FpType fpType) {
        return FpFromIeeeBvExpr.of(op, fpType);
    }

    public FpType getFpType() {
        return fpType;
    }

    @Override
    public FpType getType() {
        return fpType;
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        final BvLitExpr op = (BvLitExpr) getOp().eval(val);
        // Decompose sign ++ exponent ++ fraction with the *stored* widths -- the fraction is
        // getSignificand() - 1 bits, the implicit leading bit not being encoded. FpLitExpr.of(bv,
        // fpType) uses a different convention and would misread this, so slice it out by hand,
        // the exact inverse of FpToIeeeBvExpr#eval.
        final boolean[] bits = op.getValue();
        final int exp = fpType.getExponent();
        final int fraction = fpType.getSignificand() - 1;
        final boolean[] exponent = new boolean[exp];
        final boolean[] significand = new boolean[fraction];
        System.arraycopy(bits, 1, exponent, 0, exp);
        System.arraycopy(bits, 1 + exp, significand, 0, fraction);
        return FpLitExpr.of(
                BvLitExpr.of(new boolean[] {bits[0]}),
                BvLitExpr.of(exponent),
                BvLitExpr.of(significand));
    }

    @Override
    public FpFromIeeeBvExpr with(final Expr<BvType> op) {
        if (op == getOp()) {
            return this;
        }
        return FpFromIeeeBvExpr.of(op, fpType);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpFromIeeeBvExpr that = (FpFromIeeeBvExpr) obj;
            return this.getOp().equals(that.getOp()) && fpType.equals(that.fpType);
        } else {
            return false;
        }
    }

    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL + "[" + fpType.getExponent() + "," + fpType.getSignificand() + "]";
    }
}
