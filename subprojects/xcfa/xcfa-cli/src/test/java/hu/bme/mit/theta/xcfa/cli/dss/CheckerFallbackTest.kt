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
package hu.bme.mit.theta.xcfa.cli.dss

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.dss.CheckerFactory
import hu.bme.mit.theta.xcfa.analysis.dss.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.FastestCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.PriorityCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.actor.*
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class CheckerFallbackTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  /** x := 5; x > 3 leads to the error location: UNSAFE. */
  private val program: XCFA =
    xcfa("fallback") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "a") { "x" assign "5" }
          ("a" to err) { assume("(> x 3)") }
          ("a" to final) { assume("(<= x 3)") }
        }
      main.start()
    }

  private class SolverBroke : RuntimeException("solver broke")

  private val crashing: CheckerFactory = { _ -> throw SolverBroke() }

  private val cegar: CheckerFactory = { x ->
    getCegarChecker(
      x,
      emptySet(),
      ParseContext(),
      getDefaultPredCegarConfig(),
      NullLogger.getInstance(),
    )
  }

  private fun behavior(
    checkers: List<CheckerFactory>,
    checkerFallback: Boolean,
    roster: DssCheckerRoster = DssCheckerRoster(checkers),
  ) =
    program.procedures.single().let { procedure ->
      PredicateBlockBehavior(
        program,
        procedure,
        SingleBlockDecomposition.decompose(procedure).blocks.single(),
        roster,
        checkerFallback = checkerFallback,
      )
    }

  private fun initialMessages(
    checkers: List<CheckerFactory>,
    checkerFallback: Boolean,
    roster: DssCheckerRoster = DssCheckerRoster(checkers),
  ) = behavior(checkers, checkerFallback, roster).initialMessages()

  private fun recording(name: String, used: MutableList<String>, checker: CheckerFactory) =
    { x: XCFA ->
      used += name
      checker(x)
    }

  private val slowCegar: CheckerFactory = { x ->
    Thread.sleep(300)
    cegar(x)
  }

  @Test
  fun `a crashing checker is replaced by the next one`() {
    val messages = initialMessages(listOf(crashing, cegar), checkerFallback = true)
    assertEquals(listOf(DssMessageType.VIOLATION_CONDITION), messages.map { it.type })
  }

  @Test
  fun `without the flag the crash propagates`() {
    assertThrows(SolverBroke::class.java) {
      initialMessages(listOf(crashing, cegar), checkerFallback = false)
    }
  }

  @Test
  fun `if every checker crashes the first failure propagates with the others suppressed`() {
    val e =
      assertThrows(SolverBroke::class.java) {
        initialMessages(listOf(crashing, crashing, crashing), checkerFallback = true)
      }
    assertEquals(2, e.suppressed.size)
  }

  @Test
  fun `with priority selection the first checker runs first and the others only as fallbacks`() {
    val used = mutableListOf<String>()
    val first: CheckerFactory = { x ->
      used += "first"
      crashing(x)
    }
    val second: CheckerFactory = { x ->
      used += "second"
      cegar(x)
    }
    val third: CheckerFactory = { x ->
      used += "third"
      cegar(x)
    }
    val checkers = listOf(first, second, third)
    val roster = DssCheckerRoster(checkers, PriorityCheckerSelectionStrategy())
    repeat(2) {
      val messages = initialMessages(checkers, checkerFallback = true, roster = roster)
      assertEquals(listOf(DssMessageType.VIOLATION_CONDITION), messages.map { it.type })
    }
    assertEquals(listOf("first", "second", "first", "second"), used)
  }

  @Test
  fun `with fastest selection the first analysis runs every checker and later ones the fastest`() {
    val used = mutableListOf<String>()
    val checkers = listOf(recording("slow", used, slowCegar), recording("fast", used, cegar))
    val roster = DssCheckerRoster(checkers, FastestCheckerSelectionStrategy())
    val block = behavior(checkers, checkerFallback = false, roster = roster)
    repeat(3) {
      val messages = block.runInitialAnalysis()
      assertEquals(listOf(DssMessageType.VIOLATION_CONDITION), messages.map { it.type })
    }
    assertEquals(listOf("slow", "fast", "fast", "fast"), used)
  }

  @Test
  fun `with fastest selection the others are fallbacks even without the flag`() {
    val used = mutableListOf<String>()
    var calls = 0
    val flaky: CheckerFactory = { x -> if (calls++ == 0) cegar(x) else crashing(x) }
    val checkers = listOf(recording("flaky", used, flaky), recording("slow", used, slowCegar))
    val roster = DssCheckerRoster(checkers, FastestCheckerSelectionStrategy())
    val block = behavior(checkers, checkerFallback = false, roster = roster)
    repeat(2) {
      val messages = block.runInitialAnalysis()
      assertEquals(listOf(DssMessageType.VIOLATION_CONDITION), messages.map { it.type })
    }
    assertEquals(listOf("flaky", "slow", "flaky", "slow"), used)
  }

  @Test
  fun `with fastest selection a block whose checkers all crash tries all of them again`() {
    val used = mutableListOf<String>()
    val checkers = listOf(recording("a", used, crashing), recording("b", used, crashing))
    val roster = DssCheckerRoster(checkers, FastestCheckerSelectionStrategy())
    val block = behavior(checkers, checkerFallback = false, roster = roster)
    repeat(2) {
      val e = assertThrows(SolverBroke::class.java) { block.runInitialAnalysis() }
      assertEquals(1, e.suppressed.size)
    }
    assertEquals(listOf("a", "b", "a", "b"), used)
  }
}
