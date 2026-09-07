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
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

/**
 * `y` gets any of 0..[BOUND], more values than [LIMIT] allows, so widening turns its level into a
 * skip. The other transitions depend on `y` taking a particular value: one changes `z` below it,
 * one changes `x` above it. Both must still fire from the widened level.
 */
class MddWidenedLevelTest {

  private val x = Decls.Var("x", IntType.getInstance())
  private val y = Decls.Var("y", IntType.getInstance())
  private val z = Decls.Var("z", IntType.getInstance())

  private companion object {
    const val BOUND = 20
    const val LIMIT = 4
    const val GENEROUS_LIMIT = 10_000
  }

  private val init = And(Eq(x.ref, Int(0)), Eq(y.ref, Int(0)), Eq(z.ref, Int(0)))

  private val trans =
    Or(
      And(
        Eq(Prime(x.ref), x.ref),
        Geq(Prime(y.ref), Int(0)),
        Leq(Prime(y.ref), Int(BOUND)),
        Eq(Prime(z.ref), z.ref),
      ),
      And(
        Eq(y.ref, Int(5)),
        Eq(Prime(x.ref), x.ref),
        Eq(Prime(y.ref), y.ref),
        Eq(Prime(z.ref), Int(1)),
      ),
      And(
        Eq(y.ref, Int(7)),
        Eq(Prime(x.ref), Int(1)),
        Eq(Prime(y.ref), y.ref),
        Eq(Prime(z.ref), z.ref),
      ),
    )

  private val zStaysZero: Expr<BoolType> = Not(Eq(z.ref, Int(1)))
  private val xStaysZero: Expr<BoolType> = Not(Eq(x.ref, Int(1)))

  private fun check(prop: Expr<BoolType>, approximation: MddApproximation) =
    SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
      MddChecker(
          MonolithicExpr(init, trans, prop),
          solverPool,
          NullLogger.getInstance(),
          IterationStrategy.GSAT,
          variableOrdering = listOf(x, y, z),
          approximation = approximation,
        )
        .check(null)
    }

  @Test
  fun `both properties are violated`() {
    val exact = MddApproximation.of(MddApproximation.Strategy.NONE, GENEROUS_LIMIT)
    assertTrue(check(zStaysZero, exact).isUnsafe)
    assertTrue(check(xStaysZero, exact).isUnsafe)
  }

  @ParameterizedTest
  @EnumSource(value = MddApproximation.Strategy::class, names = ["OVER", "UNDER"])
  fun `a widened level still fires the transitions below it that depend on its value`(
    strategy: MddApproximation.Strategy
  ) {
    assertFalse(check(zStaysZero, MddApproximation.of(strategy, LIMIT)).isSafe)
  }

  @ParameterizedTest
  @EnumSource(value = MddApproximation.Strategy::class, names = ["OVER", "UNDER"])
  fun `a widened level still fires the transitions above it that depend on its value`(
    strategy: MddApproximation.Strategy
  ) {
    assertFalse(check(xStaysZero, MddApproximation.of(strategy, LIMIT)).isSafe)
  }

  /** `x` takes a nondeterministic value, and one of them leads to the violating location. */
  private val nondet =
    Or(
      And(
        Eq(y.ref, Int(0)),
        Eq(Prime(y.ref), Int(1)),
        Geq(Prime(x.ref), Int(-BOUND)),
        Leq(Prime(x.ref), Int(BOUND)),
        Eq(Prime(z.ref), z.ref),
      ),
      And(
        Eq(y.ref, Int(1)),
        Eq(x.ref, Int(7)),
        Eq(Prime(y.ref), Int(2)),
        Eq(Prime(x.ref), x.ref),
        Eq(Prime(z.ref), z.ref),
      ),
      And(
        Eq(y.ref, Int(1)),
        Not(Eq(x.ref, Int(7))),
        Eq(Prime(y.ref), Int(3)),
        Eq(Prime(x.ref), x.ref),
        Eq(Prime(z.ref), z.ref),
      ),
    )

  @Test
  fun `a widened nondeterministic value still reaches a guarded violation`() {
    for (order in listOf(listOf(y, x, z), listOf(x, y, z))) {
      SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
        val result =
          MddChecker(
              MonolithicExpr(init, nondet, Not(Eq(y.ref, Int(2)))),
              solverPool,
              NullLogger.getInstance(),
              IterationStrategy.GSAT,
              variableOrdering = order,
              approximation = MddApproximation.of(MddApproximation.Strategy.OVER, LIMIT),
            )
            .check(null)
        assertFalse(result.isSafe, "OVER proved a violated property with order $order")
      }
    }
  }
}
