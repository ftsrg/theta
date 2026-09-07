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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * A variable the initial state leaves unconstrained makes its level a skip. Plain GSAT, no
 * approximation: the answer must not depend on whether the variable happens to be bounded.
 */
class MddLevelSkipTest {

  private val loc = Decls.Var("loc", IntType.getInstance())
  private val x = Decls.Var("x", IntType.getInstance())

  /** `loc` walks 0 -> 2, then to the violating 3 exactly when `x` passes the guard. */
  private val trans =
    Or(
      And(Eq(loc.ref, Int(0)), Eq(Prime(loc.ref), Int(2)), Eq(Prime(x.ref), x.ref)),
      And(
        Eq(loc.ref, Int(2)),
        Eq(x.ref, Int(2)),
        Eq(Prime(loc.ref), Int(3)),
        Eq(Prime(x.ref), x.ref),
      ),
      And(
        Eq(loc.ref, Int(2)),
        Eq(x.ref, Int(1)),
        Eq(Prime(loc.ref), Int(1)),
        Eq(Prime(x.ref), x.ref),
      ),
      And(Eq(loc.ref, Int(1)), Eq(Prime(loc.ref), Int(1)), Eq(Prime(x.ref), x.ref)),
      And(Eq(loc.ref, Int(3)), Eq(Prime(loc.ref), Int(3)), Eq(Prime(x.ref), x.ref)),
    )

  /** `x` starts unconstrained, is written, and the written value is read back. */
  private val writeThenRead =
    Or(
      And(Eq(loc.ref, Int(0)), Eq(Prime(loc.ref), Int(1)), Eq(Prime(x.ref), Int(5))),
      And(
        Eq(loc.ref, Int(1)),
        Eq(x.ref, Int(5)),
        Eq(Prime(loc.ref), Int(3)),
        Eq(Prime(x.ref), x.ref),
      ),
      And(Eq(loc.ref, Int(3)), Eq(Prime(loc.ref), Int(3)), Eq(Prime(x.ref), x.ref)),
    )

  private fun check(constrainX: Boolean, relation: Expr<BoolType> = trans): Boolean {
    val init =
      if (constrainX) And(Eq(loc.ref, Int(0)), Geq(x.ref, Int(0)), Leq(x.ref, Int(3)))
      else Eq(loc.ref, Int(0))
    SolverPool(Z3LegacySolverFactory.getInstance()).use { solverPool ->
      return MddChecker(
          MonolithicExpr(init, relation, Not(Eq(loc.ref, Int(3)))),
          solverPool,
          NullLogger.getInstance(),
          IterationStrategy.GSAT,
          variableOrdering = listOf(loc, x),
        )
        .check(null)
        .isUnsafe
    }
  }

  @Test
  fun `a bounded variable reaches the violating location`() {
    assertTrue(check(constrainX = true))
  }

  @Test
  fun `an unconstrained variable reaches the violating location too`() {
    assertTrue(check(constrainX = false))
  }

  @Test
  fun `a write to an unconstrained variable is not lost`() {
    assertTrue(check(constrainX = false, relation = writeThenRead))
  }
}
