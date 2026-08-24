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
package hu.bme.mit.theta.core.type;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import java.math.BigInteger;
import org.junit.jupiter.api.Test;

/**
 * Subnormals decoded back out of the IEEE fields, checked against the JVM's own encoders.
 *
 * <p>A zero exponent field means two things at once -- no implicit leading 1, and an exponent of
 * {@code 1 - maxExponent} rather than the {@code -maxExponent} the field literally reads as.
 * Getting either half wrong lands the value just ABOVE the smallest normal instead of far below it,
 * so the ordering assertions here are the ones that actually bite: {@code 2^-149} used to decode as
 * {@code 2^-126 * (1 + 2^-23)} and compare GREATER than {@code FLT_MIN}. Every comparison and every
 * arithmetic fold on {@link FpLitExpr} runs through that decode, so the damage was a wrong verdict
 * (`floats-cbmc-regression/float-no-simp7`), not a lost bit of precision.
 *
 * <p>{@code Float}/{@code Double} are the oracle deliberately: an independent implementation of the
 * same standard, rather than a restatement of the code under test.
 */
public class FpSubnormalTest {

    private static final FpType FLOAT = FpType.of(8, 24);
    private static final FpType DOUBLE = FpType.of(11, 53);

    /**
     * Builds the literal by splitting a raw bit pattern into its three fields, bypassing any
     * encode-side logic -- the point is to test the DECODE in isolation.
     */
    private static FpLitExpr floatBits(int bits) {
        return FpLitExpr.of(
                (bits >>> 31) != 0,
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        BigInteger.valueOf((bits >>> 23) & 0xFF), FLOAT.getExponent()),
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        BigInteger.valueOf(bits & 0x7FFFFF), FLOAT.getSignificand() - 1));
    }

    private static FpLitExpr doubleBits(long bits) {
        return FpLitExpr.of(
                (bits >>> 63) != 0,
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        BigInteger.valueOf((bits >>> 52) & 0x7FF), DOUBLE.getExponent()),
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        BigInteger.valueOf(bits & 0xFFFFFFFFFFFFFL), DOUBLE.getSignificand() - 1));
    }

    private static float decodeFloat(FpLitExpr lit) {
        return FpUtils.fpLitExprToBigFloat(FpRoundingMode.RNE, lit).floatValue();
    }

    private static double decodeDouble(FpLitExpr lit) {
        return FpUtils.fpLitExprToBigFloat(FpRoundingMode.RNE, lit).doubleValue();
    }

    @Test
    public void testFloatSubnormalsDecodeToTheirValue() {
        // the whole subnormal range: the least one, a middle one, and the largest
        final int[] patterns = {
            0x00000001, // 2^-149, Float.MIN_VALUE
            0x00000002, // 2^-148
            0x00400000, // 2^-127
            0x007FFFFF, // largest subnormal
            0x00800000, // 2^-126, the smallest NORMAL -- the boundary the bug straddled
            0x00800001,
            0x3FC00000, // 1.5, a plain normal control
        };
        for (final int bits : patterns) {
            assertEquals(
                    Float.intBitsToFloat(bits),
                    decodeFloat(floatBits(bits)),
                    0.0f,
                    () -> String.format("float bits 0x%08x", bits));
        }
    }

    @Test
    public void testNegativeFloatSubnormalKeepsItsSign() {
        assertEquals(Float.intBitsToFloat(0x80000001), decodeFloat(floatBits(0x80000001)), 0.0f);
    }

    @Test
    public void testDoubleSubnormalsDecodeToTheirValue() {
        final long[] patterns = {
            0x0000000000000001L, // Double.MIN_VALUE, 4.9e-324
            0x0008000000000000L,
            0x000FFFFFFFFFFFFFL, // largest subnormal
            0x0010000000000000L, // smallest normal
        };
        for (final long bits : patterns) {
            assertEquals(
                    Double.longBitsToDouble(bits),
                    decodeDouble(doubleBits(bits)),
                    0.0,
                    () -> String.format("double bits 0x%016x", bits));
        }
    }

    /** The assertion the wrong verdict came from: a subnormal is BELOW the smallest normal. */
    @Test
    public void testSubnormalOrdersBelowSmallestNormal() {
        final FpLitExpr minSubnormal = floatBits(0x00000001); // 2^-149
        final FpLitExpr minNormal = floatBits(0x00800000); // 2^-126

        assertTrue(minSubnormal.lt(minNormal).getValue(), "2^-149 < 2^-126");
        assertTrue(minNormal.gt(minSubnormal).getValue(), "2^-126 > 2^-149");
        assertTrue(minSubnormal.neq(minNormal).getValue(), "2^-149 != 2^-126");

        // and subnormals order among themselves
        assertTrue(minSubnormal.lt(floatBits(0x00000002)).getValue(), "2^-149 < 2^-148");
        assertTrue(minSubnormal.gt(floatBits(0x00000000)).getValue(), "2^-149 > 0");
    }
}
