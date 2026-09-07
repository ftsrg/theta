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

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

/**
 * `x` walks 0..[BOUND] so its level exceeds any limit below BOUND + 1; `y` never leaves 0. A
 * property about `y` survives widening `x`; one about `x` does not.
 */
class MddApproximationTest {

  private val x = Decls.Var("x", IntType.getInstance())
  private val y = Decls.Var("y", IntType.getInstance())

  private companion object {
    const val BOUND = 20
    const val LIMIT = 4
    const val GENEROUS_LIMIT = 10_000
  }

  private val init = And(Eq(x.ref, Int(0)), Eq(y.ref, Int(0)))
  private val trans =
    And(
      Eq(Prime(x.ref), Add(x.ref, Int(1))),
      Leq(Prime(x.ref), Int(BOUND)),
      Eq(Prime(y.ref), y.ref),
    )

  /** Holds, and mentions only the variable that is never widened. */
  private val holdsAboutY: Expr<BoolType> = Not(Eq(y.ref, Int(1)))

  /** Holds, but only because `x` stops at [BOUND]. Widening `x` destroys it. */
  private val holdsAboutX: Expr<BoolType> = Not(Eq(x.ref, Int(BOUND + 100)))

  /** Violated: `x` does reach 5. */
  private val violated: Expr<BoolType> = Not(Eq(x.ref, Int(5)))

  private enum class Outcome {
    SAFE,
    UNSAFE,
    UNKNOWN,
  }

  private fun check(
    prop: Expr<BoolType>,
    approximation: MddApproximation,
    initExpr: Expr<BoolType> = init,
  ): Outcome {
    SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
      val result =
        MddChecker(
            MonolithicExpr(initExpr, trans, prop),
            solverPool,
            NullLogger.getInstance(),
            IterationStrategy.GSAT,
            approximation = approximation,
          )
          .check(null)
      return when {
        result.isSafe -> Outcome.SAFE
        result.isUnsafe -> Outcome.UNSAFE
        else -> Outcome.UNKNOWN
      }
    }
  }

  @Test
  fun `without a strategy the limit still gives up`() {
    assertThrows(NotSolvableException::class.java) {
      check(violated, MddApproximation.of(MddApproximation.Strategy.NONE, LIMIT))
    }
  }

  @ParameterizedTest
  @EnumSource(MddApproximation.Strategy::class)
  fun `a limit the model never reaches leaves the run exact`(strategy: MddApproximation.Strategy) {
    val approximation = MddApproximation.of(strategy, GENEROUS_LIMIT)
    assertEquals(Outcome.SAFE, check(holdsAboutY, approximation))
    assertEquals(Outcome.SAFE, check(holdsAboutX, approximation))
    assertEquals(Outcome.UNSAFE, check(violated, approximation))
    assertTrue(!approximation.isOverApproximated && !approximation.isUnderApproximated)
  }

  @ParameterizedTest
  @EnumSource(value = MddApproximation.Strategy::class, names = ["OVER", "UNDER"])
  fun `an approximated run never reports a violation of a property that holds`(
    strategy: MddApproximation.Strategy
  ) {
    assertNotEquals(
      Outcome.UNSAFE,
      check(holdsAboutY, MddApproximation.of(strategy, LIMIT)),
      "$strategy reported a violation of a property that holds",
    )
  }

  @Test
  fun `widening a level still proves a property the widened variable cannot affect`() {
    val approximation = MddApproximation.of(MddApproximation.Strategy.OVER, LIMIT)
    assertEquals(Outcome.SAFE, check(holdsAboutY, approximation))
    assertTrue(approximation.isOverApproximated)
  }

  @Test
  fun `widening a level gives up a property that depends on it`() {
    val approximation = MddApproximation.of(MddApproximation.Strategy.OVER, LIMIT)
    assertEquals(Outcome.UNKNOWN, check(holdsAboutX, approximation))
    assertTrue(approximation.isOverApproximated)
  }

  @Test
  fun `truncating a level gives up the safety proof rather than a wrong answer`() {
    val approximation = MddApproximation.of(MddApproximation.Strategy.UNDER, LIMIT)
    assertEquals(Outcome.UNKNOWN, check(holdsAboutY, approximation))
    assertTrue(approximation.isUnderApproximated)
  }

  @Test
  fun `truncating a level never proves a property that is violated`() {
    assertNotEquals(
      Outcome.SAFE,
      check(violated, MddApproximation.of(MddApproximation.Strategy.UNDER, LIMIT)),
      "UNDER proved a property that is violated",
    )
  }

  /** `x` is unconstrained in the initial state, so its level is a skip on both sides. */
  @Test
  fun `widening a level never proves a property that is violated`() {
    assertNotEquals(
      Outcome.SAFE,
      check(
        Not(Eq(x.ref, Int(7))),
        MddApproximation.of(MddApproximation.Strategy.OVER, LIMIT),
        initExpr = Eq(y.ref, Int(0)),
      ),
      "OVER proved a property that is violated",
    )
  }
}
