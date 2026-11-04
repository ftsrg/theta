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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.xcfa.model.*
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

class ByteMemoryPassTest {

  private fun bv(value: Long, size: Int) =
    BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value), size)

  @Test
  fun floatCellRefusalDoesNotRecommendAModelThatRefusesItToo() {
    // The float members of unions that reach this refusal are refused by multi and flat as well.
    val parseContext =
      ParseContext().also {
        it.memoryModel = MemoryModelType.bytes
        it.arithmetic = ArithmeticType.bitvector
      }
    val builder =
      XcfaBuilder("")
        .procedure("main") {
          val f = "f" type FpType(11, 53)
          (init to final) { Dereference.of(bv(0x310000, 64), bv(0, 64), f.type) memassign f.ref }
        }
        .builder
    val refusal =
      assertThrows<UnsupportedFrontendElementException> {
        listOf(
            NormalizePass(),
            DeterministicPass(),
            FlatMemoryPass(parseContext),
            ByteMemoryPass(parseContext),
          )
          .fold(builder) { acc, pass -> pass.runChecked(acc) }
      }
    val message = refusal.message!!
    assertFalse("Use --memory-model" in message, message)
    assertTrue("member of a union" in message, message)
  }
}
