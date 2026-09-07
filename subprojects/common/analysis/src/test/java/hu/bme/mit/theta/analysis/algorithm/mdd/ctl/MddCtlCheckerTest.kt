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
package hu.bme.mit.theta.analysis.algorithm.mdd.ctl

import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** Counter model: x in {0,1,2,3}, init x=0, x' = x+1 while x<3, self-loop at x=3. */
class MddCtlCheckerTest {

  private val x = Decls.Var("x", IntType.getInstance())

  private fun atom(e: Expr<BoolType>): CtlExpr = CtlExpr.Atom(e)

  private val xIs0 = atom(Eq(x.ref, Int(0)))
  private val xIs1 = atom(Eq(x.ref, Int(1)))
  private val xIs2 = atom(Eq(x.ref, Int(2)))
  private val xIs3 = atom(Eq(x.ref, Int(3)))
  private val xLt2 = atom(Lt(x.ref, Int(2)))
  private val xLt3 = atom(Lt(x.ref, Int(3)))

  private fun <T> withChecker(
    euStrategy: MddCtlChecker.EuStrategy = MddCtlChecker.EuStrategy.CONSTRAINED_SATURATION,
    block: (MddCtlChecker) -> T,
  ): T {
    val init = Eq(x.ref, Int(0))
    val trans =
      Or(
        And(Lt(x.ref, Int(3)), Eq(Prime(x.ref), Add(x.ref, Int(1)))),
        And(Eq(x.ref, Int(3)), Eq(Prime(x.ref), x.ref)),
      )
    val prop = True()
    val monolithicExpr = MonolithicExpr(init, trans, prop)
    SolverPool(Z3LegacySolverFactory.getInstance()).use { pool ->
      return block(
        MddCtlChecker(monolithicExpr, pool, NullLogger.getInstance(), euStrategy = euStrategy)
      )
    }
  }

  private fun count(c: MddCtlChecker, e: CtlExpr): Long =
    MddInterpreter.calculateNonzeroCount(c.check(e))

  @Test
  fun stateSpaceHasFourStates() = withChecker { c ->
    assertEquals(4L, MddInterpreter.calculateNonzeroCount(c.stateSpace))
    assertEquals(1L, count(c, xIs3))
    assertEquals(3L, count(c, xLt3))
  }

  @Test
  fun exactSetSizes() = withChecker { c ->
    // only state 0 has a successor where x=1
    assertEquals(1L, count(c, CtlExpr.EX(xIs1)))
    // every state reaches 3
    assertEquals(4L, count(c, CtlExpr.EF(xIs3)))
    // the only x=3 cycle is the self-loop at 3
    assertEquals(1L, count(c, CtlExpr.EG(xIs3)))
    // every state has an infinite path
    assertEquals(4L, count(c, CtlExpr.EG(CtlExpr.Top)))
    // 0,1,2 stay <3 and reach 3; 3 is already there
    assertEquals(4L, count(c, CtlExpr.EU(xLt3, xIs3)))
    // only state 3 qualifies; 0/1 cannot reach 3 without passing through x=2
    assertEquals(1L, count(c, CtlExpr.EU(xLt2, xIs3)))
  }

  @Test
  fun satisfactionAtInitialState() = withChecker { c ->
    assertTrue(c.isSatisfied(CtlExpr.EF(xIs3)))
    assertTrue(c.isSatisfied(CtlExpr.EX(xIs1)))
    assertFalse(c.isSatisfied(CtlExpr.EX(xIs2)))
    assertTrue(c.isSatisfied(CtlExpr.AF(xIs3)))
    assertFalse(c.isSatisfied(CtlExpr.EG(xIs3)))
    assertTrue(c.isSatisfied(CtlExpr.AG(xLt3.let { CtlExpr.Or(it, xIs3) })))
    assertFalse(c.isSatisfied(CtlExpr.AG(CtlExpr.Not(xIs2))))
    assertFalse(c.isSatisfied(CtlExpr.AG(CtlExpr.EF(xIs0))))
  }

  @Test
  fun euStrategiesAgree() {
    val formulas =
      listOf(
        CtlExpr.EU(xLt3, xIs3),
        CtlExpr.EU(xLt2, xIs3),
        CtlExpr.EF(xIs3),
        CtlExpr.AU(xLt3, xIs3),
        CtlExpr.AG(CtlExpr.EF(xIs0)),
      )
    val saturation =
      withChecker(MddCtlChecker.EuStrategy.CONSTRAINED_SATURATION) { c ->
        formulas.map { count(c, it) }
      }
    val fixpointLoop =
      withChecker(MddCtlChecker.EuStrategy.FIXPOINT_LOOP) { c -> formulas.map { count(c, it) } }
    assertEquals(saturation, fixpointLoop)
  }

  @Test
  fun dualitiesHoldAsSets() = withChecker { c ->
    // AG p == !EF !p
    val p = CtlExpr.Or(xLt3, xIs3)
    assertEquals(c.check(CtlExpr.AG(p)).node, c.check(CtlExpr.Not(CtlExpr.EF(CtlExpr.Not(p)))).node)
    // AF p == !EG !p
    assertEquals(
      c.check(CtlExpr.AF(xIs3)).node,
      c.check(CtlExpr.Not(CtlExpr.EG(CtlExpr.Not(xIs3)))).node,
    )
    // EF p == E[Top U p]
    assertEquals(c.check(CtlExpr.EF(xIs3)).node, c.check(CtlExpr.EU(CtlExpr.Top, xIs3)).node)
  }
}
