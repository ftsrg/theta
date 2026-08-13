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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.fptype.FpExprs.NaN;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.NegativeInfinity;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.PositiveInfinity;

import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import java.math.BigInteger;
import java.math.RoundingMode;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

public final class FpUtils {

    private FpUtils() {}

    public static BigFloat fpLitExprToBigFloat(
            final FpRoundingMode roundingMode, final FpLitExpr expr) {
        if (expr.isNaN()) {
            return BigFloat.NaN(expr.getType().getSignificand());
        } else if (expr.isPositiveInfinity()) {
            return BigFloat.positiveInfinity(expr.getType().getSignificand());
        } else if (expr.isNegativeInfinity()) {
            return BigFloat.negativeInfinity(expr.getType().getSignificand());
        } else if (expr.isPositiveZero()) {
            return BigFloat.zero(expr.getType().getSignificand());
        } else if (expr.isNegativeZero()) {
            return BigFloat.negativeZero(expr.getType().getSignificand());
        } else {
            final var maxExponent = (1L << (expr.getType().getExponent() - 1)) - 1;

            final var exponentField = BvUtils.neutralBvLitExprToBigInteger(expr.getExponent());
            final var significandField = BvUtils.neutralBvLitExprToBigInteger(expr.getSignificand());

            // An all-zero exponent field marks a SUBNORMAL, and IEEE-754 encodes those differently
            // in two ways at once: there is no implicit leading 1, and the exponent is the smallest
            // *normal* one (1 - maxExponent) rather than the -maxExponent the field literally reads
            // as. Decoding them as normals -- adding the hidden bit and taking the exponent a step
            // too low -- turned every subnormal into a value just ABOVE the smallest normal:
            // 2^-149 came back as 2^-126*(1+2^-23) instead of 1.4e-45. Since this function backs
            // every comparison and every arithmetic fold on FpLitExpr, `x < FLT_MIN` was then false
            // for every subnormal x, and theta answered the gradual-underflow tests wrongly rather
            // than imprecisely (`floats-cbmc-regression/float-no-simp7`).
            // Zeroes never reach here -- they are handled above -- but sign*0 would decode
            // correctly anyway, the significand field being 0.
            final var subnormal = exponentField.signum() == 0;
            final var exponent =
                    subnormal
                            ? BigInteger.valueOf(1 - maxExponent)
                            : exponentField.subtract(BigInteger.valueOf(maxExponent));
            final var significand =
                    subnormal
                            ? significandField
                            : significandField.add(
                                    BigInteger.TWO.pow(expr.getType().getSignificand() - 1));

            return new BigFloat(
                    expr.getHidden(),
                    significand,
                    exponent.longValue(),
                    getMathContext(expr.getType(), roundingMode));
        }
    }

    public static FpLitExpr bigFloatToFpLitExpr(final BigFloat bigFloat, final FpType type) {
        if (bigFloat.isNaN()) {
            return NaN(type);
        } else if (bigFloat.isInfinite()
                && bigFloat.greaterThan(BigFloat.zero(type.getSignificand()))) {
            return PositiveInfinity(type);
        } else if (bigFloat.isInfinite()
                && bigFloat.lessThan(BigFloat.zero(type.getSignificand()))) {
            return NegativeInfinity(type);
        } else {
            final var minExponent = -(1L << (type.getExponent() - 1)) + 2;
            final var maxExponent = (1L << (type.getExponent() - 1)) - 1;
            final var round =
                    bigFloat.round(getMathContext(type, FpRoundingMode.getDefaultRoundingMode()));

            final var exponent =
                    BigInteger.valueOf(round.exponent(minExponent, maxExponent))
                            .add(BigInteger.valueOf(maxExponent));
            final var significand = round.significand(minExponent, maxExponent);

            return FpLitExpr.of(
                    bigFloat.sign(),
                    BvUtils.bigIntegerToNeutralBvLitExpr(exponent, type.getExponent()),
                    BvUtils.bigIntegerToNeutralBvLitExpr(significand, type.getSignificand() - 1));
        }
    }

    public static RoundingMode getMathContextRoundingMode(final FpRoundingMode roundingMode) {
        if (roundingMode == null) {
            return RoundingMode.UNNECESSARY;
        }

        switch (roundingMode) {
            case RNE:
                return RoundingMode.HALF_EVEN;
            case RNA:
                return RoundingMode.UP;
            case RTP:
                return RoundingMode.CEILING;
            case RTN:
                return RoundingMode.FLOOR;
            case RTZ:
                return RoundingMode.DOWN;
            default:
                throw new UnsupportedOperationException();
        }
    }

    public static BinaryMathContext getMathContext(
            final FpType type, final FpRoundingMode roundingMode) {
        return new BinaryMathContext(
                type.getSignificand(),
                type.getExponent(),
                getMathContextRoundingMode(roundingMode));
    }

    public static FpLitExpr fromString(final String value, final FpType type) {
        return bigFloatToFpLitExpr(
                new BigFloat(
                        value, new BinaryMathContext(type.getSignificand(), type.getExponent())),
                type);
    }

    public static BigInteger round(final BigFloat value, final FpRoundingMode roundingMode) {
        RoundingMode r = FpUtils.getMathContextRoundingMode(roundingMode);
        return value.toBigInteger(r);
    }
}
