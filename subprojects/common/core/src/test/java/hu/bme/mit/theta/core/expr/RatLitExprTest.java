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
package hu.bme.mit.theta.core.expr;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class RatLitExprTest {
    public int num;
    public int denom;
    public int expectedfloor;
    public int expectedCeil;
    public int expectedSign;
    public int expectedFracNum;
    public int expectedFracDenom;

    public RatLitExpr number;

    public RatLitExpr expectedFrac;

    public void initialize() {
        // Arrange
        number = Rat(num, denom);
        expectedFrac = Rat(expectedFracNum, expectedFracDenom);
    }

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {0, 1, 0, 0, 0, 0, 1},
                    {1, 1, 1, 1, 1, 0, 1},
                    {1, 2, 0, 1, 1, 1, 2},
                    {-1, 2, -1, 0, -1, 1, 2},
                    {-1, 1, -1, -1, -1, 0, 1},
                    {3, 2, 1, 2, 1, 1, 2},
                    {-3, 2, -2, -1, -1, 1, 2}
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testFloor(
            int num,
            int denom,
            int expectedfloor,
            int expectedCeil,
            int expectedSign,
            int expectedFracNum,
            int expectedFracDenom) {
        initRatLitExprTest(
                num,
                denom,
                expectedfloor,
                expectedCeil,
                expectedSign,
                expectedFracNum,
                expectedFracDenom);
        // Act
        final var actualFloor = number.floor();
        // Assert
        assertEquals(BigInteger.valueOf(expectedfloor), actualFloor);
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testCeil(
            int num,
            int denom,
            int expectedfloor,
            int expectedCeil,
            int expectedSign,
            int expectedFracNum,
            int expectedFracDenom) {
        initRatLitExprTest(
                num,
                denom,
                expectedfloor,
                expectedCeil,
                expectedSign,
                expectedFracNum,
                expectedFracDenom);
        // Act
        final var actualCeil = number.ceil();
        // Assert
        assertEquals(BigInteger.valueOf(expectedCeil), actualCeil);
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testSign(
            int num,
            int denom,
            int expectedfloor,
            int expectedCeil,
            int expectedSign,
            int expectedFracNum,
            int expectedFracDenom) {
        initRatLitExprTest(
                num,
                denom,
                expectedfloor,
                expectedCeil,
                expectedSign,
                expectedFracNum,
                expectedFracDenom);
        // Act
        final long actualSign = number.sign();
        // Assert
        assertEquals(expectedSign, actualSign);
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testFrac(
            int num,
            int denom,
            int expectedfloor,
            int expectedCeil,
            int expectedSign,
            int expectedFracNum,
            int expectedFracDenom) {
        initRatLitExprTest(
                num,
                denom,
                expectedfloor,
                expectedCeil,
                expectedSign,
                expectedFracNum,
                expectedFracDenom);
        // Act
        final RatLitExpr actualFrac = number.frac();
        // Assert
        assertEquals(expectedFrac, actualFrac);
    }

    public void initRatLitExprTest(
            int num,
            int denom,
            int expectedfloor,
            int expectedCeil,
            int expectedSign,
            int expectedFracNum,
            int expectedFracDenom) {
        this.num = num;
        this.denom = denom;
        this.expectedfloor = expectedfloor;
        this.expectedCeil = expectedCeil;
        this.expectedSign = expectedSign;
        this.expectedFracNum = expectedFracNum;
        this.expectedFracDenom = expectedFracDenom;
        this.initialize();
    }
}
