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
package hu.bme.mit.theta.core.type;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Abs;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Leq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sub;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNE;
import static org.junit.jupiter.api.Assertions.*;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpTestUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import java.util.Collection;
import java.util.stream.Collectors;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.kframework.mpfr.BigFloat;

public class FpTypeTest {
    public Class<?> exprType;
    public Expr<?> expected;
    public Expr<?> actual;

    public static Collection<?> operations() {
        return FpTestUtils.GetOperations().collect(Collectors.toUnmodifiableList());
    }

    @MethodSource("operations")
    @ParameterizedTest(name = "expr: {0}, expected: {1}, actual: {2}")
    public void testFp(Class<?> exprType, Expr<?> expected, Expr<?> actual) {
        initFpTypeTest(exprType, expected, actual);
        // Sanity check
        assertNotNull(exprType);
        assertNotNull(expected);
        assertNotNull(actual);

        // Type checks
        assertTrue(
                exprType.isInstance(actual),
                "The type of actual is "
                        + actual.getClass().getName()
                        + " instead of "
                        + exprType.getName());
        assertEquals(
                expected.getType(),
                actual.getType(),
                "The type of expected ("
                        + expected.getType()
                        + ") must match the type of actual ("
                        + actual.getType()
                        + ")");

        // Equality check
        Valuation val = ImmutableValuation.builder().build();
        if (expected instanceof FpLitExpr && actual.getType() instanceof FpType) {
            if (((FpLitExpr) expected).isNaN()) {
                assertTrue(((FpLitExpr) actual.eval(val)).isNaN());
            } else if (((FpLitExpr) expected).isNegativeInfinity()) {
                assertTrue(((FpLitExpr) actual.eval(val)).isNegativeInfinity());
            } else if (((FpLitExpr) expected).isPositiveInfinity()) {
                assertTrue(((FpLitExpr) actual.eval(val)).isPositiveInfinity());
            } else {
                //noinspection unchecked
                FpLeqExpr leq =
                        Leq(
                                Abs(
                                        Sub(
                                                RNE,
                                                (FpLitExpr) expected,
                                                (Expr<FpType>) actual.eval(val))),
                                FpUtils.bigFloatToFpLitExpr(
                                        new BigFloat(
                                                "1e-2",
                                                FpUtils.getMathContext(
                                                        (FpType) actual.getType(), RNE)),
                                        (FpType) actual.getType()));
                assertEquals(Bool(true), leq.eval(val), "%s".formatted(actual.eval(val)));
            }
        } else {
            assertEquals(expected, actual.eval(val));
        }
    }

    public void initFpTypeTest(Class<?> exprType, Expr<?> expected, Expr<?> actual) {
        this.exprType = exprType;
        this.expected = expected;
        this.actual = actual;
    }
}
