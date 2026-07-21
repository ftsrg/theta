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

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpExprs;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import java.math.BigInteger;
import org.junit.jupiter.api.Test;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

/**
 * The IEEE-754 bit reinterpretation, checked against the JVM's own {@code Double}/{@code Float}
 * encoders -- the point of these expressions is bit-exactness, so the oracle has to be an
 * independent implementation of the same standard, not a restatement of the code under test.
 */
public class FpIeeeBvTest {

    private static final FpType DOUBLE = FpType.of(11, 53);
    private static final FpType FLOAT = FpType.of(8, 24);

    private FpLitExpr doubleLit(double value) {
        return FpUtils.bigFloatToFpLitExpr(
                new BigFloat(value, new BinaryMathContext(53, 11)), DOUBLE);
    }

    private FpLitExpr floatLit(float value) {
        return FpUtils.bigFloatToFpLitExpr(
                new BigFloat(value, new BinaryMathContext(24, 8)), FLOAT);
    }

    private long evalBits(FpLitExpr lit) {
        final BvLitExpr bv =
                (BvLitExpr) FpExprs.ToIeeeBv(lit).eval(ImmutableValuation.empty());
        // longValue() keeps the low 64 bits as two's complement -- the raw pattern, so a value with
        // the sign bit set (a negative double) does not overflow the way longValueExact would.
        return BvUtils.unsignedBvLitExprToBigInteger(bv).longValue();
    }

    @Test
    void toIeeeBvMatchesDoubleToLongBits() {
        for (double v : new double[] {1.0, 0.0, -1.0, 2.5, -0.5, 1e300, 3.14159265358979}) {
            assertEquals(
                    Double.doubleToLongBits(v),
                    evalBits(doubleLit(v)),
                    "IEEE double bits of " + v);
        }
    }

    @Test
    void toIeeeBvMatchesFloatToIntBits() {
        for (float v : new float[] {1.0f, 0.0f, -1.0f, 2.5f, -0.5f, 3.14159f}) {
            final BvLitExpr bv =
                    (BvLitExpr) FpExprs.ToIeeeBv(floatLit(v)).eval(ImmutableValuation.empty());
            final long bits = BvUtils.unsignedBvLitExprToBigInteger(bv).longValueExact();
            assertEquals(Float.floatToIntBits(v) & 0xFFFFFFFFL, bits, "IEEE float bits of " + v);
        }
    }

    @Test
    void fromIeeeBvInvertsToIeeeBv() {
        for (double v : new double[] {1.0, -1.0, 2.5, -0.5, 42.0, 1e100}) {
            final BvLitExpr bits =
                    BvUtils.bigIntegerToUnsignedBvLitExpr(
                            BigInteger.valueOf(Double.doubleToLongBits(v)), 64);
            final FpLitExpr back =
                    (FpLitExpr)
                            FpExprs.FromIeeeBv(bits, DOUBLE).eval(ImmutableValuation.empty());
            assertEquals(
                    v,
                    FpUtils.fpLitExprToBigFloat(FpRoundingMode.RNE, back).doubleValue(),
                    "round trip of " + v);
        }
    }
}
