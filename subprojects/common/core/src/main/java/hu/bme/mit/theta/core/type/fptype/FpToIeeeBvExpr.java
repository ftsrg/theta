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

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;

/**
 * The raw IEEE-754 bit pattern of a floating-point value, as a bitvector of the same width -- a
 * *reinterpretation*, not a numeric conversion. This is what {@code fpToIEEEBV} in Z3 does, and what
 * the kernel/newlib idiom {@code union { double value; uint64_t bits; }} needs: {@code bits} is the
 * exact encoding of {@code value}, so {@code 1.0} becomes {@code 0x3FF0000000000000}, not {@code 1}.
 *
 * <p>Distinct from {@link FpToBvExpr}, which rounds the *value* to an integer ({@code (uint64_t)1.0
 * == 1}). The result width is fixed by the float's format -- sign + exponent + significand -- so
 * this carries no rounding mode and no signedness.
 */
public class FpToIeeeBvExpr extends UnaryExpr<FpType, BvType> {

    private static final int HASH_SEED = 6817;
    private static final String OPERATOR_LABEL = "fptoieeebv";

    private FpToIeeeBvExpr(final Expr<FpType> op) {
        super(op);
    }

    public static FpToIeeeBvExpr of(final Expr<FpType> op) {
        return new FpToIeeeBvExpr(op);
    }

    public static FpToIeeeBvExpr create(final Expr<FpType> op) {
        return FpToIeeeBvExpr.of(op);
    }

    /**
     * The bitvector width the float's format encodes to.
     *
     * <p>{@code getSignificand()} counts the implicit leading bit, which IEEE does not store, so the
     * on-the-wire fraction is {@code getSignificand() - 1} bits. With the sign bit the total is
     * {@code 1 + exponent + (significand - 1) == exponent + significand}: 64 for double
     * {@code FpType.of(11, 53)}, 32 for float {@code FpType.of(8, 24)}. (Not {@code + 1} more --
     * {@code FpLitExpr.of(bv, fpType)} uses a different, incompatible convention; do not route
     * through it.)
     */
    public static int bitWidth(final FpType fpType) {
        return fpType.getExponent() + fpType.getSignificand();
    }

    @Override
    public BvType getType() {
        return BvType.of(bitWidth(getOp().getType()));
    }

    @Override
    public BvLitExpr eval(final Valuation val) {
        final FpLitExpr op = (FpLitExpr) getOp().eval(val);
        // sign ++ exponent ++ significand -- exactly the order FpLitExpr.of(bv, fpType) reads back.
        final boolean[] exponent = op.getExponent().getValue();
        final boolean[] significand = op.getSignificand().getValue();
        final boolean[] bits = new boolean[1 + exponent.length + significand.length];
        bits[0] = op.getHidden();
        System.arraycopy(exponent, 0, bits, 1, exponent.length);
        System.arraycopy(significand, 0, bits, 1 + exponent.length, significand.length);
        return BvLitExpr.of(bits);
    }

    @Override
    public FpToIeeeBvExpr with(final Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        }
        return FpToIeeeBvExpr.of(op);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpToIeeeBvExpr that = (FpToIeeeBvExpr) obj;
            return this.getOp().equals(that.getOp());
        } else {
            return false;
        }
    }

    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }
}
