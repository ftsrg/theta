/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
import static org.junit.Assert.assertEquals;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.type.rattype.RatLitExpr;

@RunWith(Parameterized.class)
public final class RatLitExprTest {

	@Parameter(value = 0)
	public int num;

	@Parameter(value = 1)
	public int denom;

	@Parameter(value = 2)
	public int expectedfloor;

	@Parameter(value = 3)
	public int expectedCeil;

	@Parameter(value = 4)
	public int expectedSign;

	@Parameter(value = 5)
	public int expectedFracNum;

	@Parameter(value = 6)
	public int expectedFracDenom;

	public RatLitExpr number;

	public RatLitExpr expectedFrac;

	@Before
	public void initialize() {
		// Arrange
		number = Rat(num, denom);
		expectedFrac = Rat(expectedFracNum, expectedFracDenom);
	}

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{0, 1, 0, 0, 0, 0, 1},

				{1, 1, 1, 1, 1, 0, 1},

				{1, 2, 0, 1, 1, 1, 2},

				{-1, 2, -1, 0, -1, 1, 2},

				{-1, 1, -1, -1, -1, 0, 1},

				{3, 2, 1, 2, 1, 1, 2},

				{-3, 2, -2, -1, -1, 1, 2}

		});
	}

	@Test
	public void testFloor() {
		// Act
		final var actualFloor = number.floor();
		// Assert
		assertEquals(BigInteger.valueOf(expectedfloor), actualFloor);
	}

	@Test
	public void testCeil() {
		// Act
		final var actualCeil = number.ceil();
		// Assert
		assertEquals(BigInteger.valueOf(expectedCeil), actualCeil);
	}

	@Test
	public void testSign() {
		// Act
		final long actualSign = number.sign();
		// Assert
		assertEquals(expectedSign, actualSign);
	}

	@Test
	public void testFrac() {
		// Act
		final RatLitExpr actualFrac = number.frac();
		// Assert
		assertEquals(expectedFrac, actualFrac);
	}

}
