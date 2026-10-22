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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

/** Havocs written as `x' = s` for a symbol `s`, so only the symbolic mode can enumerate them. */
class MddSymbolicValuesTest {

  private val int = IntType.getInstance()
  private val loc = Decls.Var("loc", int)
  private val x = Decls.Var("x", int)
  private val y = Decls.Var("y", int)
  private val s = Decls.Const("s", int)
  private val t = Decls.Const("t", int)

  private enum class Outcome {
    SAFE,
    UNSAFE,
    UNKNOWN,
  }

  private fun unchanged(vararg vars: VarDecl<*>): Expr<BoolType> =
    And(vars.map { Eq(Prime(it.ref), it.ref) })

  private fun step(from: Int, to: Int, vararg body: Expr<BoolType>): Expr<BoolType> =
    And(listOf(Eq(loc.ref, Int(from)), Eq(Prime(loc.ref), Int(to))) + body)

  private fun <T> permutations(list: List<T>): List<List<T>> =
    if (list.size <= 1) listOf(list)
    else list.flatMap { head -> permutations(list - head).map { listOf(head) + it } }

  /** The outcome, which must be the same under every variable order. */
  private fun check(init: Expr<BoolType>, vararg events: Expr<BoolType>, error: Int): Outcome {
    val monolithicExpr = MonolithicExpr(init, Or(events.toList()), Neq(loc.ref, Int(error)))
    val outcomes =
      permutations(monolithicExpr.vars).associateWith { order ->
        SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
          val result =
            MddChecker(
                monolithicExpr,
                solverPool,
                NullLogger.getInstance(),
                IterationStrategy.GSAT,
                variableOrdering = order,
                symbolicValues = true,
              )
              .check(null)
          when {
            result.isSafe -> Outcome.SAFE
            result.isUnsafe -> Outcome.UNSAFE
            else -> Outcome.UNKNOWN
          }
        }
      }
    assertEquals(1, outcomes.values.toSet().size, "outcome depends on the order: $outcomes")
    return outcomes.values.first()
  }

  private val start = And(Eq(loc.ref, Int(0)), Eq(x.ref, Int(0)), Eq(y.ref, Int(0)))

  @Test
  fun `a guard on a havoced value is reached`() {
    val outcome =
      check(
        start,
        step(0, 1, Eq(Prime(x.ref), s.ref), unchanged(y)),
        step(1, 2, Eq(x.ref, Int(7)), unchanged(x, y)),
        step(1, 3, Neq(x.ref, Int(7)), unchanged(x, y)),
        error = 2,
      )
    assertEquals(Outcome.UNSAFE, outcome)
  }

  @Test
  fun `a copy keeps the correlation`() {
    val outcome =
      check(
        start,
        step(0, 1, Eq(Prime(x.ref), s.ref), unchanged(y)),
        step(1, 2, Eq(Prime(y.ref), x.ref), unchanged(x)),
        step(2, 3, Neq(x.ref, y.ref), unchanged(x, y)),
        error = 3,
      )
    assertEquals(Outcome.SAFE, outcome)
  }

  @Test
  fun `a copied concrete value reaches the error`() {
    val outcome =
      check(
        start,
        step(0, 1, Eq(Prime(x.ref), Int(5)), unchanged(y)),
        step(1, 2, Eq(Prime(y.ref), x.ref), unchanged(x)),
        step(2, 3, Eq(y.ref, Int(5)), unchanged(x, y)),
        error = 3,
      )
    assertEquals(Outcome.UNSAFE, outcome)
  }

  @Test
  fun `a copy within one step reaches the error`() {
    val outcome =
      check(
        start,
        step(0, 1, Eq(Prime(x.ref), Int(5)), Eq(Prime(y.ref), Prime(x.ref))),
        step(1, 2, Eq(y.ref, Int(5)), unchanged(x, y)),
        error = 2,
      )
    assertEquals(Outcome.UNSAFE, outcome)
  }

  @Test
  fun `a later step on the copy reaches the error`() {
    val outcome =
      check(
        start,
        step(0, 1, Eq(Prime(x.ref), Int(5)), unchanged(y)),
        step(1, 2, Eq(Prime(y.ref), x.ref), unchanged(x)),
        step(2, 3, Eq(Prime(x.ref), Int(6)), unchanged(y)),
        step(3, 4, Eq(y.ref, Int(5)), Eq(x.ref, Int(6)), unchanged(x, y)),
        error = 4,
      )
    assertEquals(Outcome.UNSAFE, outcome)
  }

  @Test
  fun `a value computed from a symbol keeps its definition`() {
    val events =
      arrayOf(
        step(0, 1, Eq(Prime(x.ref), s.ref), unchanged(y)),
        step(1, 2, Eq(Prime(y.ref), Add(x.ref, Int(1))), unchanged(x)),
      )
    assertEquals(
      Outcome.SAFE,
      check(start, *events, step(2, 3, Neq(y.ref, Add(x.ref, Int(1))), unchanged(x, y)), error = 3),
    )
    assertEquals(
      Outcome.UNSAFE,
      check(start, *events, step(2, 3, Eq(y.ref, Int(8)), unchanged(x, y)), error = 3),
    )
  }

  @Test
  fun `values computed from different symbols get different names`() {
    val w = Decls.Var("w", int)
    val outcome =
      check(
        And(start, Eq(w.ref, Int(0))),
        step(0, 1, Eq(Prime(x.ref), s.ref), unchanged(y, w)),
        step(1, 2, Eq(Prime(y.ref), Add(x.ref, Int(1))), unchanged(x, w)),
        step(2, 3, Eq(Prime(x.ref), t.ref), unchanged(y, w)),
        step(3, 4, Eq(Prime(w.ref), Add(x.ref, Int(1))), unchanged(x, y)),
        step(4, 5, Neq(Sub(y.ref, w.ref), Sub(s.ref, t.ref)), unchanged(x, y, w)),
        error = 5,
      )
    assertEquals(Outcome.SAFE, outcome)
  }

  @Test
  fun `branches split the path condition`() {
    val outcome =
      check(
        start,
        step(0, 1, Eq(Prime(x.ref), s.ref), unchanged(y)),
        step(1, 2, Gt(x.ref, Int(10)), Eq(Prime(y.ref), x.ref), unchanged(x)),
        step(1, 2, Not(Gt(x.ref, Int(10))), Eq(Prime(y.ref), Int(10)), unchanged(x)),
        step(2, 3, Lt(y.ref, Int(10)), unchanged(x, y)),
        error = 3,
      )
    assertEquals(Outcome.SAFE, outcome)
  }

  @Test
  fun `differences of two inputs have opposite signs`() {
    val outcome =
      check(
        start,
        step(0, 1, Eq(Prime(x.ref), Sub(s.ref, t.ref)), Eq(Prime(y.ref), Sub(t.ref, s.ref))),
        step(1, 2, Gt(x.ref, Int(0)), Gt(y.ref, Int(0)), unchanged(x, y)),
        error = 2,
      )
    assertEquals(Outcome.SAFE, outcome)
  }

  @Test
  fun `a spin on a symbolic flag closes the loop`() {
    // loc is the spinning thread, y the one clearing the flag x
    val init = And(Eq(loc.ref, Int(0)), Eq(x.ref, Int(0)), Eq(y.ref, Int(0)))
    val events =
      arrayOf(
        step(0, 1, Eq(Prime(x.ref), s.ref), unchanged(y)),
        step(1, 1, Neq(x.ref, Int(0)), unchanged(x, y)),
        step(1, 2, Eq(x.ref, Int(0)), unchanged(x, y)),
        And(
          Eq(y.ref, Int(0)),
          Neq(loc.ref, Int(0)),
          Eq(Prime(y.ref), Int(1)),
          Eq(Prime(x.ref), Int(0)),
          unchanged(loc),
        ),
      )
    assertEquals(
      Outcome.SAFE,
      check(init, *events, step(2, 3, Neq(x.ref, Int(0)), unchanged(x, y)), error = 3),
    )
    assertEquals(
      Outcome.UNSAFE,
      check(init, *events, step(2, 3, Eq(y.ref, Int(0)), unchanged(x, y)), error = 3),
    )
  }

  @Test
  fun `bitvector symbols are keys too`() {
    val bv = BvType.of(32)
    val b = Decls.Var("b", bv)
    val u = Decls.Const("u", bv)
    val ones = Bv(BooleanArray(32) { true })
    val outcome =
      check(
        And(Eq(loc.ref, Int(0)), Eq(b.ref, Bv(BooleanArray(32)))),
        step(0, 1, Eq(Prime(b.ref), u.ref)),
        step(1, 2, Eq(b.ref, ones), unchanged(b)),
        error = 2,
      )
    assertEquals(Outcome.UNSAFE, outcome)
  }
}
