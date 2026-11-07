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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression

import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class LitExprConverterTest {

  private fun roundTrip(lit: LitExpr<*>): LitExpr<*> =
    LitExprConverter.toLitExpr(LitExprConverter.toInt(lit), lit.type)

  @Test
  fun `integers round-trip, also outside the int range`() {
    for (value in
      listOf(
        "0",
        "-1",
        "1073741823",
        "1073741824",
        "2147483647",
        "2147483648",
        "-2147483648",
        "-2147483649",
        "4294967295",
        "4294967296",
        "-4294967296",
        "18446744073709551616",
      )) {
      assertEquals(Int(value), roundTrip(Int(value)), value)
    }
  }

  @Test
  fun `integers that agree in the low 32 bits get different keys`() {
    val keys = listOf("0", "4294967296", "-4294967296").map { LitExprConverter.toInt(Int(it)) }
    assertEquals(keys.size, keys.toSet().size)
  }

  @Test
  fun `bitvectors round-trip`() {
    for (size in listOf(8, 32, 64)) {
      val type = BvType.of(size)
      for (value in
        listOf("0", "1", "2147483647", "2147483648", "4294967295", "18446744073709551615")) {
        val big = BigInteger(value)
        if (big.bitLength() > size) continue
        val lit = BvUtils.bigIntegerToNeutralBvLitExpr(big, size)
        assertEquals(lit, roundTrip(lit), "$value on $size bits")
      }
    }
  }

  @Test
  fun `a wide key no value was given is invalid`() {
    val unused = Int.MIN_VALUE + (1 shl 16) - 1
    assertTrue(LitExprConverter.toLitExpr(unused, IntType.getInstance()).isInvalid)
    assertTrue(LitExprConverter.toLitExpr(unused, BvType.of(64)).isInvalid)
  }
}
