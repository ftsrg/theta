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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.addressesAtomicData
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Under flat addressing, `_Atomic` cells are recognised both before [FlatMemoryPass] (where
 * [DataRaceToReachabilityPass] asks) and after it (where the CEGAR data-race check asks).
 */
class FlatAtomicAccessTest {

  private val stride = FlatMemoryPass.FLAT_STRIDE

  // Object 1 is atomic as a whole, object 4 only in cell 2 (FrontendXcfaBuilder mints 3k+1 ids).
  private val parseContext =
    ParseContext().also {
      it.memoryModel = MemoryModelType.flat
      it.arithmetic = ArithmeticType.integer
      it.markObjectFullyAtomic(BigInteger.ONE)
      it.markObjectAtomicCell(BigInteger.valueOf(4), 2)
    }

  private fun deref(array: Long, offset: Long) =
    Dereference.of(Int(array.toInt()), Int(offset.toInt()), Int())

  private fun Dereference<*, *, *>.atomic() = addressesAtomicData(emptyList(), parseContext)

  @Test
  fun unflattenedAddressIsDecoded() {
    assertTrue(deref(stride, 0).atomic())
    assertTrue(deref(stride, 3).atomic())
    assertTrue(deref(4 * stride, 2).atomic())
    assertFalse(deref(4 * stride, 1).atomic())
    assertFalse(deref(7 * stride, 0).atomic())
    assertFalse(Dereference.of(Var("p", Int()).ref, Int(0), Int()).atomic())
  }

  @Test
  fun flattenedAddressIsDecoded() {
    assertTrue(deref(0, stride).atomic())
    assertTrue(deref(0, 4 * stride + 2).atomic())
    assertFalse(deref(0, 4 * stride + 1).atomic())
  }

  /** 5*STRIDE + (-4*STRIDE) wraps to STRIDE, as FlatMemoryPass folds it: a cell of object 1. */
  @Test
  fun bitvectorAddressWraps() {
    fun bv(value: Long) = BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value), 32)
    val folded = ExprUtils.simplify(BvExprs.Add(listOf(bv(5 * stride), bv(-4 * stride))))
    assertTrue(Dereference.of(bv(5 * stride), bv(-4 * stride), BvType.of(32)).atomic())
    assertTrue(Dereference.of(bv(0), folded, BvType.of(32)).atomic())
  }

  /** Main and a thread it started both write the cell at [address]. */
  private fun raceReachable(address: String): Boolean {
    val model =
      xcfa("") {
        val thr = procedure("thr") { (init to final) { "(deref $address Int)" memassign "1" } }
        val main =
          procedure("main") {
            "t" type Int()
            (init to "L1") { "t".start(thr) }
            ("L1" to final) { "(deref $address Int)" memassign "2" }
          }
        main.start()
      }
    val property = XcfaProperty(ErrorDetection.DATA_RACE)
    val passes =
      listOf(
        DataRaceToReachabilityPass(property, parseContext, enabled = true),
        FlatMemoryPass(parseContext),
      )
    return model.optimizeFurther(ProcedurePassManager(passes)).procedures.any {
      it.errorLoc.isPresent && it.errorLoc.get().incomingEdges.isNotEmpty()
    }
  }

  @Test
  fun atomicCellIsNotInstrumented() {
    assertFalse(raceReachable("$stride 0"))
    assertFalse(raceReachable("${4 * stride} 2"))
  }

  @Test
  fun plainCellIsInstrumented() {
    assertTrue(raceReachable("${4 * stride} 1"))
    assertTrue(raceReachable("${7 * stride} 0"))
  }
}
