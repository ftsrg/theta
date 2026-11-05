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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Add
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Geq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Gt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Leq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Mul
import hu.bme.mit.theta.core.type.inttype.IntExprs.Sub
import hu.bme.mit.theta.core.utils.ExprUtils
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class CInvariantExportTest {

  companion object {
    private val aDecl = Var("a", Int())
    private val bDecl = Var("b", Int())
    private val a = aDecl.ref
    private val b = bDecl.ref

    private fun int(v: Long) = Int(BigInteger.valueOf(v))

    private val noRange: (hu.bme.mit.theta.core.decl.VarDecl<*>) -> Pair<BigInteger, BigInteger>? =
      {
        null
      }

    @JvmStatic
    fun conjunctions(): List<List<Expr<BoolType>>> =
      listOf(
        listOf(Leq(a, b), Leq(b, a)),
        listOf(Geq(Sub(a, b), int(0)), Leq(int(0), Sub(b, a))),
        listOf(Leq(a, int(2)), Leq(a, int(3))),
        listOf(Leq(a, b), Lt(b, a)),
        listOf(Gt(a, int(1)), Not(Gt(a, int(2)))),
        listOf(Not(Leq(a, b)), Not(Geq(a, Add(b, int(2))))),
        listOf(Geq(Add(a, Mul(int(-2), b)), int(0)), Leq(a, Mul(int(2), b))),
        listOf(Or(Eq(a, b), Gt(a, b))),
        listOf(Or(Eq(a, b), Lt(a, b))),
        listOf(Or(Eq(a, b), Gt(Sub(b, a), int(0)))),
        listOf(Or(Eq(a, Sub(b, int(1))), Gt(a, b))),
        listOf(Or(Eq(a, b), Eq(a, Add(b, int(1))), Gt(a, Add(b, int(1))))),
        listOf(Or(Eq(a, Sub(b, int(1))), Eq(a, b), Geq(a, Add(b, int(1))))),
        listOf(Or(Leq(a, b), Geq(a, Add(b, int(3))))),
        listOf(Or(Leq(a, b), Geq(a, b))),
      )

    private fun holds(conjuncts: List<Expr<BoolType>>, x: Long, y: Long): Boolean {
      val valuation = ImmutableValuation.builder().put(aDecl, int(x)).put(bDecl, int(y)).build()
      return ExprUtils.simplify(And(conjuncts), valuation) ==
        hu.bme.mit.theta.core.type.booltype.BoolExprs.True()
    }
  }

  @ParameterizedTest
  @MethodSource("conjunctions")
  fun testMergeKeepsTheMeaning(conjuncts: List<Expr<BoolType>>) {
    val merged = mergeBounds(conjuncts, noRange)
    for (x in -6L..6L) for (y in -6L..6L) {
      assertEquals(holds(conjuncts, x, y), holds(merged, x, y)) {
        "$conjuncts -> $merged at $x, $y"
      }
    }
  }

  @Test
  fun testOppositeBoundsBecomeAnEquality() {
    assertEquals(listOf(Eq(b, a)), mergeBounds(listOf(Leq(a, b), Leq(b, a)), noRange))
  }

  @Test
  fun testOnlyTheTightestBoundStays() {
    assertEquals(
      listOf(Leq(a, int(2))),
      mergeBounds(listOf(Leq(a, int(2)), Leq(a, int(3))), noRange),
    )
  }

  @Test
  fun testAdjoiningRangesBecomeOneBound() {
    assertEquals(listOf(Geq(a, b)), mergeBounds(listOf(Or(Eq(a, b), Gt(a, b))), noRange))
  }

  @Test
  fun testRangesWithAGapStay() {
    val gap = Or(Eq(a, Sub(b, int(1))), Gt(a, b))
    assertEquals(listOf(gap), mergeBounds(listOf(gap), noRange))
  }

  @Test
  fun testBoundsImpliedByTheTypeAreDropped() {
    val range = { _: hu.bme.mit.theta.core.decl.VarDecl<*> ->
      BigInteger.valueOf(-2147483648L) to BigInteger.valueOf(2147483647L)
    }
    assertEquals(
      emptyList<Expr<BoolType>>(),
      mergeBounds(listOf(Geq(Add(a, int(2147483649L)), int(0))), range),
    )
    assertEquals(listOf(Geq(a, int(0))), mergeBounds(listOf(Geq(a, int(0))), range))
  }
}
