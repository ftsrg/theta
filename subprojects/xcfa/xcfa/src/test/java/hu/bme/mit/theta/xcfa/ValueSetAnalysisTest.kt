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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvExprs.URem
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.ValueSetAnalysis
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class ValueSetAnalysisTest {

  private fun values(
    expr: String,
    zeroInitialized: Boolean = true,
    maxValues: Int = 64,
    procedure: String = "main",
    model: XcfaBuilder.() -> Unit,
  ): Set<Int>? {
    val xcfa = XcfaBuilder("test").apply(model)
    val analysis = ValueSetAnalysis(xcfa, zeroInitialized, maxValues)
    val e = xcfa.getProcedures().first { it.name == procedure }.parse(expr)
    return analysis.values(e)?.map { (it as IntLitExpr).value.toInt() }?.toSet()
  }

  @Test
  fun `every assignment reaches every read`() {
    val result =
      values("y") {
        procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "L") { "x" assign "1" }
            (init to "L") { "x" assign "2" }
            ("L" to final) { "y" assign "x" }
          }
          .start()
      }
    assertEquals(setOf(1, 2), result)
  }

  @Test
  fun `a local read before its first write is unknown`() {
    val result =
      values("x") {
        procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "L") { "y" assign "x" }
            ("L" to final) { "x" assign "1" }
          }
          .start()
      }
    assertNull(result)
  }

  @Test
  fun `an assumption on an uninitialized local does not make it unknown`() {
    val result =
      values("x") {
        procedure("main") {
            "x" type Int()
            (init to "L") { assume("(> x 0)") }
            ("L" to final) { "x" assign "1" }
          }
          .start()
      }
    assertEquals(setOf(1), result)
  }

  @Test
  fun `a havoc makes a variable unknown`() {
    val result =
      values("x") {
        procedure("main") {
            "x" type Int()
            (init to "L") { "x" assign "1" }
            ("L" to final) { havoc("x") }
          }
          .start()
      }
    assertNull(result)
  }

  @Test
  fun `a variable a call writes is unknown`() {
    val result =
      values("x") {
        val f =
          procedure("f") {
            ("r" type Int()).direction(ParamDirection.OUT)
            (init to final) { "r" assign "2" }
          }
        procedure("main") {
            "x" type Int()
            (init to "L") { "x" assign "1" }
            ("L" to final) { f("x") }
          }
          .start()
      }
    assertNull(result)
  }

  @Test
  fun `an unbounded counter becomes unknown`() {
    val result =
      values("i") {
        procedure("main") {
            "i" type Int()
            (init to "L") { "i" assign "0" }
            ("L" to "L") { "i" assign "(+ i 1)" }
            ("L" to final) { assume("true") }
          }
          .start()
      }
    assertNull(result)
  }

  @Test
  fun `a set over the limit is unknown`() {
    val result =
      values("x", maxValues = 2) {
        procedure("main") {
            "x" type Int()
            (init to final) { "x" assign "1" }
            (init to final) { "x" assign "2" }
            (init to final) { "x" assign "3" }
          }
          .start()
      }
    assertNull(result)
  }

  @Test
  fun `a remainder by a literal is bounded even if the dividend is unknown`() {
    val result =
      values("y") {
        procedure("main") {
            "x" type Int()
            "y" type Int()
            (init to "L") { havoc("x") }
            ("L" to final) { "y" assign "(mod x 4)" }
          }
          .start()
      }
    assertEquals(setOf(0, 1, 2, 3), result)
  }

  @Test
  fun `a global gets its initial value and the writes of every thread`() {
    val result =
      values("g") {
        global { "g" type Int() init "0" }
        val thr1 = procedure("thr1") { (init to final) { "g" assign "1" } }
        val thr2 = procedure("thr2") { (init to final) { "g" assign "2" } }
        procedure("main") {
            "t1" type Int()
            "t2" type Int()
            (init to final) {
              "t1".start(thr1)
              "t2".start(thr2)
            }
          }
          .start()
      }
    assertEquals(setOf(0, 1, 2), result)
  }

  @Test
  fun `a thread parameter gets the start arguments`() {
    val result =
      values("p", procedure = "thr") {
        val thr =
          procedure("thr") {
            ("r" type Int()).direction(ParamDirection.OUT)
            ("p" type Int()).direction(ParamDirection.IN)
            (init to final) { assume("true") }
          }
        procedure("main") {
            "t" type Int()
            (init to final) { "t".start(thr, "0", "5") }
          }
          .start()
      }
    assertEquals(setOf(5), result)
  }

  @Test
  fun `a cell starts from zero only if memory is zero-initialized`() {
    val model: XcfaBuilder.() -> Unit = {
      procedure("main") { (init to final) { "(deref 1 0 Int)" memassign "7" } }.start()
    }
    assertEquals(setOf(0, 7), values("(deref 1 0 Int)", model = model))
    assertNull(values("(deref 1 0 Int)", zeroInitialized = false, model = model))
  }

  @Test
  fun `a cell written through a computed address keeps its initial value`() {
    val result =
      values("(deref 1 1 Int)") {
        global { "i" type Int() init "0" }
        val thr = procedure("thr") { (init to final) { "i" assign "1" } }
        procedure("main") {
            "t" type Int()
            (init to "L") { "t".start(thr) }
            ("L" to final) { "(deref 1 i Int)" memassign "7" }
          }
          .start()
      }
    assertEquals(setOf(0, 7), result)
  }

  @Test
  fun `a write to an unknown address makes its partition unknown`() {
    val result =
      values("(deref 1 0 Int)") {
        procedure("main") {
            "j" type Int()
            (init to "L") { "(deref 1 0 Int)" memassign "7" }
            ("L" to "M") { havoc("j") }
            ("M" to final) { "(deref 1 j Int)" memassign "8" }
          }
          .start()
      }
    assertNull(result)
  }

  @Test
  fun `an expression takes every combination of the values of its operands`() {
    val result =
      values("z") {
        procedure("main") {
            "x" type Int()
            "y" type Int()
            "z" type Int()
            (init to "L") { "x" assign "1" }
            (init to "L") { "x" assign "2" }
            ("L" to "M") { "y" assign "10" }
            ("L" to "M") { "y" assign "20" }
            ("M" to final) { "z" assign "(+ x y)" }
          }
          .start()
      }
    assertEquals(setOf(11, 12, 21, 22), result)
  }

  @Test
  fun `an expression with too many combinations is unknown`() {
    val result =
      values("z", maxValues = 3) {
        procedure("main") {
            "x" type Int()
            "y" type Int()
            "z" type Int()
            (init to "L") { "x" assign "1" }
            (init to "L") { "x" assign "2" }
            ("L" to "M") { "y" assign "10" }
            ("L" to "M") { "y" assign "20" }
            ("M" to final) { "z" assign "(+ x y)" }
          }
          .start()
      }
    assertNull(result)
  }

  @Test
  fun `a variable no assignment writes is unknown, even with an initial value`() {
    val result =
      values("g") {
        global { "g" type Int() init "5" }
        procedure("main") { (init to final) { assume("true") } }.start()
      }
    assertNull(result)
  }

  @Test
  fun `a read through a bounded address joins the values of its cells`() {
    val result =
      values("x") {
        global { "i" type Int() init "0" }
        val thr = procedure("thr") { (init to final) { "i" assign "1" } }
        procedure("main") {
            "t" type Int()
            "x" type Int()
            (init to "L") { "t".start(thr) }
            ("L" to "M") { "(deref 1 0 Int)" memassign "7" }
            ("M" to "N") { "(deref 1 1 Int)" memassign "8" }
            ("N" to final) { "x" assign "(deref 1 i Int)" }
          }
          .start()
      }
    assertEquals(setOf(0, 7, 8), result)
  }

  @Test
  fun `a bitvector remainder keeps the type of its operands`() {
    val type = BvType.of(8, true)
    lateinit var x: VarDecl<*>
    val xcfa =
      XcfaBuilder("test").apply {
        procedure("main") {
            x = "x" type type
            (init to final) { havoc("x") }
          }
          .start()
      }
    val four = Bv(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(4), 8).value, true)
    val result = ValueSetAnalysis(xcfa, true).values(URem(cast(x.ref, type), four))!!
    assertEquals(
      (0..3).map { BigInteger.valueOf(it.toLong()) }.toSet(),
      result.map { BvUtils.neutralBvLitExprToBigInteger(it as BvLitExpr) }.toSet(),
    )
    assertTrue(result.all { it.type == type })
  }
}
