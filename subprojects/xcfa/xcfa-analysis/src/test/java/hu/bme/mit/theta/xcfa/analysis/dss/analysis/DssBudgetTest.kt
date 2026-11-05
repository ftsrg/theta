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
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

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
  fun `a budget needs two checkers and a strategy that does not rank them per block`() {
    val checkers = List(2) { i -> { _: XCFA -> error("stub checker $i must never be invoked") } }
    assertTrue(DssCheckerRoster(checkers, budgetMs = 50).budgeted)
    assertFalse(DssCheckerRoster(checkers).budgeted)
    assertFalse(DssCheckerRoster(checkers.take(1), budgetMs = 50).budgeted)
    assertFalse(DssCheckerRoster(checkers, FastestCheckerSelectionStrategy(), 50).budgeted)
    assertThrows(IllegalArgumentException::class.java) { DssCheckerRoster(checkers, budgetMs = -1) }
  }
}
