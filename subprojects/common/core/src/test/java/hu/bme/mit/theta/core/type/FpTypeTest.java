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
package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpTestUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.kframework.mpfr.BigFloat;

import java.util.Collection;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Abs;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Leq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sub;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

@RunWith(Parameterized.class)
public class FpTypeTest {

    @Parameterized.Parameter(0)
    public Class<?> exprType;

    @Parameterized.Parameter(1)
    public Expr<?> expected;

    @Parameterized.Parameter(2)
    public Expr<?> actual;

    @Parameterized.Parameters(name = "expr: {0}, expected: {1}, actual: {2}")
    public static Collection<?> operations() {
        return FpTestUtils.GetOperations().collect(Collectors.toUnmodifiableList());
    }

    @Test
    public void testFp() {
        // Sanity check
        assertNotNull(exprType);
        assertNotNull(expected);
        assertNotNull(actual);

        // Type checks
        assertTrue(
                "The type of actual is " + actual.getClass().getName() + " instead of "
                        + exprType.getName(),
                exprType.isInstance(actual)
        );
        assertEquals(
                "The type of expected (" + expected.getType() + ") must match the type of actual ("
                        + actual.getType() + ")",
                expected.getType(),
                actual.getType()
        );

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
                FpLeqExpr leq = Leq(
                        Abs(Sub(RNE, (FpLitExpr) expected, (Expr<FpType>) actual.eval(val))),
                        FpUtils.bigFloatToFpLitExpr(new BigFloat("1e-2",
                                        FpUtils.getMathContext((FpType) actual.getType(), RNE)),
                                (FpType) actual.getType()));
                assertEquals(Bool(true), leq.eval(val));
            }
        } else {
            assertEquals(expected, actual.eval(val));
        }
    }
}
