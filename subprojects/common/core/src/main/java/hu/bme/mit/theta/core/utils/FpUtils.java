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
package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;
import java.math.RoundingMode;

import static hu.bme.mit.theta.core.type.fptype.FpExprs.NaN;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.NegativeInfinity;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.PositiveInfinity;

public final class FpUtils {

    private FpUtils() {
    }

    public static BigFloat fpLitExprToBigFloat(final FpRoundingMode roundingMode,
                                               final FpLitExpr expr) {
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

            final var exponent = BvUtils.neutralBvLitExprToBigInteger(expr.getExponent())
                    .subtract(BigInteger.valueOf(maxExponent));
            final var significand = BvUtils.neutralBvLitExprToBigInteger(expr.getSignificand())
                    .add(BigInteger.TWO.pow(expr.getType().getSignificand() - 1));

            return new BigFloat(expr.getHidden(), significand, exponent.longValue(),
                    getMathContext(expr.getType(), roundingMode));
        }
    }

    public static FpLitExpr bigFloatToFpLitExpr(final BigFloat bigFloat, final FpType type) {
        if (bigFloat.isNaN()) {
            return NaN(type);
        } else if (bigFloat.isInfinite() && bigFloat.greaterThan(
                BigFloat.zero(type.getSignificand()))) {
            return PositiveInfinity(type);
        } else if (bigFloat.isInfinite() && bigFloat.lessThan(
                BigFloat.zero(type.getSignificand()))) {
            return NegativeInfinity(type);
        } else {
            final var minExponent = -(1L << (type.getExponent() - 1)) + 2;
            final var maxExponent = (1L << (type.getExponent() - 1)) - 1;
            final var round = bigFloat.round(getMathContext(type, FpRoundingMode.RNE));

            final var exponent = BigInteger.valueOf(round.exponent(minExponent, maxExponent))
                    .add(BigInteger.valueOf(maxExponent));
            final var significand = round.significand(minExponent, maxExponent);

            return FpLitExpr.of(
                    bigFloat.sign(),
                    BvUtils.bigIntegerToNeutralBvLitExpr(exponent, type.getExponent()),
                    BvUtils.bigIntegerToNeutralBvLitExpr(significand, type.getSignificand() - 1)
            );
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

    public static BinaryMathContext getMathContext(final FpType type,
                                                   final FpRoundingMode roundingMode) {
        return new BinaryMathContext(type.getSignificand(), type.getExponent(),
                getMathContextRoundingMode(roundingMode));
    }

    public static FpLitExpr fromString(final String value, final FpType type) {
        return bigFloatToFpLitExpr(new BigFloat(
                        value,
                        new BinaryMathContext(
                                type.getExponent(),
                                type.getSignificand())),
                type);
    }
}
