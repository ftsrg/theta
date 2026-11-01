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
package hu.bme.mit.theta.xcfa

import hu.bme.mit.theta.core.type.fptype.FpExprs
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Test

/** Witness values are printed as C constants of the variable's type. */
class CConstraintTest {

  private val parseContext = ParseContext()

  private fun type(name: String) = CComplexType.getType(name, parseContext)

  private fun bv(value: Long, width: Int) =
    BvUtils.bigIntegerToNeutralBvLitExpr(
      BigInteger.valueOf(value).mod(BigInteger.TWO.pow(width)),
      width,
    )

  private val double = FpType.of(11, 53)
  private val float = FpType.of(8, 24)

  @Test
  fun testIntegersKeepTheSignednessOfTheirType() {
    assertEquals("x == -1", bv(-1, 8).toCConstraint("x", type("char")))
    assertEquals("x == 255U", bv(-1, 8).toCConstraint("x", type("unsignedchar")))
    assertEquals("x == 4294967295U", bv(-1, 32).toCConstraint("x", type("unsignedint")))
    assertEquals(
      "x == (-2147483647-1)",
      bv(Int.MIN_VALUE.toLong(), 32).toCConstraint("x", type("int")),
    )
    assertEquals(
      "x == (-9223372036854775807LL-1)",
      bv(Long.MIN_VALUE, 64).toCConstraint("x", type("longlong")),
    )
    assertEquals("x == -5", Int(-5).toCConstraint("x", type("int")))
    assertEquals(
      "x == 3000000000LL",
      Int(BigInteger.valueOf(3000000000L)).toCConstraint("x", type("longlong")),
    )
  }

  @Test
  fun testFloatsIncludingNaNAndInfinities() {
    assertEquals("x == -2.5", FpUtils.fromString("-2.5", double).toCConstraint("x", type("double")))
    assertEquals("x == 0.5f", FpUtils.fromString("0.5", float).toCConstraint("x", type("float")))
    assertEquals("x != x", FpExprs.NaN(double).toCConstraint("x", type("double")))
    assertEquals(
      "x > 1.7976931348623157e+308",
      FpExprs.PositiveInfinity(double).toCConstraint("x", type("double")),
    )
    assertEquals(
      "x < -3.4028234663852886e+38f",
      FpExprs.NegativeInfinity(float).toCConstraint("x", type("float")),
    )
  }

  @Test
  fun testValuesWithoutAnExactConstantAreOmitted() {
    assertNull(FpUtils.fromString("1.5", FpType.of(15, 113)).toCConstraint("x", type("longdouble")))
    assertNull(bv(4, 32).toCConstraint("p", type("int*")))
    assertNull(bv(4, 32).toCConstraint("x", null))
  }
}
