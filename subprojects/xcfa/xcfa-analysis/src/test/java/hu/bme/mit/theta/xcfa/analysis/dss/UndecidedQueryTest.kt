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
package hu.bme.mit.theta.xcfa.analysis.dss

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Gt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Mul
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.UnknownSolverStatusException
import java.lang.reflect.Proxy
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** Queries the solver cannot decide, as Z3 on nonlinear arithmetic. */
class UndecidedQueryTest {

  /** A factory whose solvers answer every check with [check]; counts the solvers created. */
  private class StubFactory(private val check: () -> SolverStatus) {
    var created = 0
    val factory =
      Proxy.newProxyInstance(
        SolverFactory::class.java.classLoader,
        arrayOf(SolverFactory::class.java),
      ) { _, _, _ ->
        created++
        Proxy.newProxyInstance(Solver::class.java.classLoader, arrayOf(Solver::class.java)) {
          _,
          m,
          _ ->
          if (m.name == "check") check() else null
        }
      } as SolverFactory
  }

  private val unknown = StubFactory { throw UnknownSolverStatusException() }
  private val crashing = StubFactory { throw IllegalStateException("native crash") }
  private val unsat = StubFactory { SolverStatus.UNSAT }
  private val sat = StubFactory { SolverStatus.SAT }

  private val x = Var("x", IntType.getInstance()).ref
  private val nonlinear = Gt(Mul(x, x), Int(10))

  @Test
  fun `every undecided query fails`() {
    for (factory in listOf(unknown.factory, crashing.factory)) {
      val operators = DssPredicateOperators(factory)
      assertThrows(DssUndecidedQueryException::class.java) { operators.isUnsat(nonlinear) }
      assertThrows(DssUndecidedQueryException::class.java) {
        operators.isLeq(nonlinear, Lt(x, Int(3)))
      }
    }
  }

  @Test
  fun `decided queries`() {
    assertTrue(DssPredicateOperators(unsat.factory).isUnsat(nonlinear))
    assertFalse(DssPredicateOperators(sat.factory).isUnsat(nonlinear))
    assertTrue(DssPredicateOperators(unsat.factory).isLeq(nonlinear, Eq(x, Int(0))))
  }

  @Test
  fun `a failed solver is replaced`() {
    val operators = DssPredicateOperators(unknown.factory)
    repeat(3) { runCatching { operators.isUnsat(nonlinear) } }
    assertEquals(3, unknown.created)
  }

  @Test
  fun `trivial cases need no solver`() {
    val operators = DssPredicateOperators(unknown.factory)
    assertTrue(operators.isLeq(nonlinear, True()))
    assertTrue(operators.isLeq(nonlinear, nonlinear))
    assertEquals(0, unknown.created)
  }
}
