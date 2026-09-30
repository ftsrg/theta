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

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/**
 * The flat and bytes memory models build their addresses after the last [SimplifyExprsPass], so the
 * address of a statically known cell must be folded to one literal there -- not left as the sum of
 * the object's base and the cell's offset.
 */
class FlatMemoryPassTest {

  private fun context(model: MemoryModelType, arithmetic: ArithmeticType) =
    ParseContext().also {
      it.memoryModel = model
      it.arithmetic = arithmetic
    }

  private fun runPasses(
    passes: List<ProcedurePass>,
    input: XcfaProcedureBuilderContext.() -> Unit,
  ): XcfaProcedureBuilder {
    val builder = XcfaBuilder("").procedure("main", input).builder
    return (listOf(NormalizePass(), DeterministicPass()) + passes).fold(builder) { acc, pass ->
      pass.runChecked(acc)
    }
  }

  private fun XcfaProcedureBuilder.derefs(): List<Dereference<*, *, *>> =
    getEdges().flatMap { edge ->
      edge.getFlatLabels().flatMap { label ->
        when (val stmt = (label as? StmtLabel)?.stmt) {
          is MemoryAssignStmt<*, *, *> -> listOf(stmt.deref) + stmt.expr.derefs()
          is AssumeStmt -> stmt.cond.derefs()
          else -> emptyList()
        }
      }
    }

  private fun Expr<*>.derefs(): List<Dereference<*, *, *>> =
    (if (this is Dereference<*, *, *>) listOf(this) else emptyList()) + ops.flatMap { it.derefs() }

  private fun bv(value: Long, size: Int) =
    BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value), size)

  @Test
  fun integerAddressIsFolded() {
    val parseContext = context(MemoryModelType.flat, ArithmeticType.integer)
    val result =
      runPasses(listOf(FlatMemoryPass(parseContext))) {
        (init to "L1") { "(deref 65536 1 Int)" memassign "42" }
        ("L1" to final) { assume("(= (deref 65536 1 Int) 42)") }
      }
    val derefs = result.derefs()
    assertEquals(2, derefs.size)
    derefs.forEach {
      assertEquals(Int(0), it.array)
      assertEquals(Int(65537), it.offset)
    }
  }

  @Test
  fun bitvectorAddressIsFolded() {
    // The shape reported in the issue: object 49 (base 0x310000) at cell 1, with 64-bit pointers.
    val parseContext = context(MemoryModelType.flat, ArithmeticType.bitvector)
    val cell = Dereference.of(bv(0x310000, 64), bv(1, 64), BvType(32))
    val result =
      runPasses(listOf(FlatMemoryPass(parseContext))) {
        (init to final) { cell memassign bv(42, 32) }
      }
    val deref = result.derefs().single()
    assertEquals(bv(0, 64), deref.array)
    assertEquals(bv(0x310001, 64), deref.offset)
  }

  @Test
  fun pointerPlusZeroIsFolded() {
    val parseContext = context(MemoryModelType.flat, ArithmeticType.integer)
    val result =
      runPasses(listOf(FlatMemoryPass(parseContext))) {
        "p" type Int()
        (init to final) { "(deref p 0 Int)" memassign "42" }
      }
    val deref = result.derefs().single()
    assertEquals(result.getVars().single { it.name == "p" }.ref, deref.offset)
  }

  @Test
  fun byteCellAddressesAreFolded() {
    val parseContext = context(MemoryModelType.bytes, ArithmeticType.bitvector)
    val cell = Dereference.of(bv(0x310000, 64), bv(4, 64), BvType(32))
    val result =
      runPasses(listOf(FlatMemoryPass(parseContext), ByteMemoryPass(parseContext))) {
        (init to final) { cell memassign bv(42, 32) }
      }
    val derefs = result.derefs()
    assertEquals((0x310004L..0x310007L).map { bv(it, 64) }, derefs.map { it.offset })
    derefs.forEach { assertEquals(bv(0, 64), it.array) }
  }

  @Test
  fun floatCellRefusalDoesNotRecommendAModelThatRefusesItToo() {
    // The float members of unions that reach this refusal are refused by multi and flat as well.
    val parseContext = context(MemoryModelType.bytes, ArithmeticType.bitvector)
    val refusal =
      assertThrows<UnsupportedFrontendElementException> {
        runPasses(listOf(FlatMemoryPass(parseContext), ByteMemoryPass(parseContext))) {
          val f = "f" type FpType(11, 53)
          (init to final) { Dereference.of(bv(0x310000, 64), bv(0, 64), f.type) memassign f.ref }
        }
      }
    val message = refusal.message!!
    assertFalse("Use --memory-model" in message, message)
    assertTrue("member of a union" in message, message)
  }
}
