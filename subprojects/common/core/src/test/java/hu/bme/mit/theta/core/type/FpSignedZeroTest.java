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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import java.math.BigInteger;
import org.junit.jupiter.api.Test;

/** The sign of a floating-point zero survives decoding and the arithmetic folds built on it. */
public class FpSignedZeroTest {

    private static final FpType FLOAT = FpType.of(8, 24);

    private static FpLitExpr floatBits(int bits) {
        return FpLitExpr.of(
                (bits >>> 31) != 0,
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        BigInteger.valueOf((bits >>> 23) & 0xFF), FLOAT.getExponent()),
                BvUtils.bigIntegerToUnsignedBvLitExpr(
                        BigInteger.valueOf(bits & 0x7FFFFF), FLOAT.getSignificand() - 1));
    }

    private static int decodedBits(FpLitExpr lit) {
        return Float.floatToRawIntBits(
                FpUtils.fpLitExprToBigFloat(FpRoundingMode.RNE, lit).floatValue());
    }

    @Test
    public void testZeroSign() {
        final FpLitExpr positive = floatBits(Float.floatToRawIntBits(0.0f));
        final FpLitExpr negative = floatBits(Float.floatToRawIntBits(-0.0f));

        assertTrue(positive.isPositiveZero());
        assertFalse(positive.isNegativeZero());
        assertTrue(negative.isNegativeZero());
        assertFalse(negative.isPositiveZero());

        assertEquals(Float.floatToRawIntBits(0.0f), decodedBits(positive));
        assertEquals(Float.floatToRawIntBits(-0.0f), decodedBits(negative));
    }

    @Test
    public void testDivisionByZeroTakesItsSign() {
        final FpLitExpr one = floatBits(Float.floatToRawIntBits(1.0f));

        assertTrue(
                one.div(FpRoundingMode.RNE, floatBits(Float.floatToRawIntBits(0.0f)))
                        .isPositiveInfinity());
        assertTrue(
                one.div(FpRoundingMode.RNE, floatBits(Float.floatToRawIntBits(-0.0f)))
                        .isNegativeInfinity());
    }
}
