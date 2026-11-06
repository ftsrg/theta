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
package hu.bme.mit.theta.xcfa.analysis.dss.analysis

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.UnknownSolverStatusException
import hu.bme.mit.theta.xcfa.analysis.dss.HangingSolverFactory
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import java.time.Duration
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource

class DssBudgetTest {

  private fun overrun(budgetMs: Long, check: () -> Unit) =
    DssDeadline.within(budgetMs) {
      Thread.sleep(budgetMs + 20)
      check()
    }

  @Test
  fun `the deadline throws only once the budget is spent`() {
    DssDeadline.within(10_000) { DssDeadline.check() }
    assertThrows(DssBudgetExceededException::class.java) { overrun(1) { DssDeadline.check() } }
  }

  @Test
  fun `a nested deadline applies only inside, and no deadline means no limit`() {
    overrun(1) {
      DssDeadline.within(null) { DssDeadline.check() }
      assertThrows(DssBudgetExceededException::class.java) { DssDeadline.check() }
    }
    DssDeadline.check()
  }

  @Test
  fun `an overrun is recognized through the exceptions wrapping it`() {
    assertTrue(
      RuntimeException(IllegalStateException(DssBudgetExceededException(5))).isDssBudgetExceeded()
    )
    assertFalse(RuntimeException(IllegalStateException()).isDssBudgetExceeded())
  }

  @Test
  fun `a deadline solver checks the budget before each query`() {
    ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    DeadlineSolverManager.ensureRegistered("Z3")
    val factory = SolverManager.resolveSolverFactory(DeadlineSolverManager.nameFor("Z3"))
    for (solver in
      listOf(factory.createSolver(), factory.createUCSolver(), factory.createItpSolver())) {
      assertEquals(SolverStatus.SAT, solver.check())
      assertThrows(DssBudgetExceededException::class.java) { overrun(1) { solver.check() } }
      solver.close()
    }
  }

  @Test
  fun `a deadline interrupts a query still running when it passes`() {
    val solver = DeadlineSolverFactory(HangingSolverFactory).createSolver()
    val e =
      assertThrows(DssBudgetExceededException::class.java) {
        DssDeadline.within(50) { solver.check() }
      }
    assertTrue(e.cause is UnknownSolverStatusException) { "$e" }
  }

  @Test
  fun `an exception leaving an expired deadline is an overrun, and before it only itself`() {
    val late = assertThrows(DssBudgetExceededException::class.java) { overrun(1) { error("late") } }
    assertTrue(late.cause is IllegalStateException) { "$late" }
    assertThrows(IllegalStateException::class.java) {
      DssDeadline.within(10_000) { error("early") }
    }
  }

  /** [holes] + 1 pigeons, each in a hole, no two in the same one: unsatisfiable, hard to refute. */
  private fun pigeonhole(holes: Int): List<Expr<BoolType>> {
    val sits = List(holes + 1) { p -> List(holes) { h -> Const("p${p}h$h", Bool()).ref } }
    val placed = sits.map { Or(it) }
    val apart =
      (0 until holes).flatMap { h ->
        (0..holes).flatMap { p -> (p + 1..holes).map { q -> Not(And(sits[p][h], sits[q][h])) } }
      }
    return placed + apart
  }

  @ParameterizedTest
  @ValueSource(strings = ["Z3", "Z3:new", "JavaSMT:MATHSAT5"])
  fun `a deadline stops a long query of an interruptible backend`(name: String) {
    ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    DeadlineSolverManager.ensureRegistered(name)
    val factory = SolverManager.resolveSolverFactory(DeadlineSolverManager.nameFor(name))
    val solver = factory.createSolver()
    solver.add(pigeonhole(12))
    assertTimeoutPreemptively(Duration.ofSeconds(30)) {
      assertThrows(DssBudgetExceededException::class.java) {
        DssDeadline.within(200) { solver.check() }
      }
    }
    solver.close()
  }

  @Test
  fun `a budget needs two checkers and a strategy that does not rank them per block`() {
    val checkers = List(2) { i -> { _: XCFA -> error("stub checker $i must never be invoked") } }
    assertTrue(DssCheckerRoster(checkers, budgetMs = 50).budgeted)
    assertFalse(DssCheckerRoster(checkers).budgeted)
    assertFalse(DssCheckerRoster(checkers.take(1), budgetMs = 50).budgeted)
    assertFalse(DssCheckerRoster(checkers, FastestCheckerSelectionStrategy(), 50).budgeted)
    assertThrows(IllegalArgumentException::class.java) { DssCheckerRoster(checkers, budgetMs = -1) }
  }
}
