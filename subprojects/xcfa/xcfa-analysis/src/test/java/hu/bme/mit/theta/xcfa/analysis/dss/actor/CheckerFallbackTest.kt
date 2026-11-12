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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.dss.HangingSolverFactory
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DeadlineSolverFactory
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssBlockCutRequest
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssDeadline
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.FastestCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.FinisherCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.PriorityCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.ensureDefaultSolversRegistered
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

  /** x := 5; x > 3 on a single edge into the error location: a block without a cut. */
  private val uncuttable: XCFA =
    xcfa("uncuttable") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to err) {
            "x" assign "5"
            assume("(> x 3)")
          }
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
    cutOnTimeout: Boolean = false,
    xcfa: XCFA = program,
  ) =
    xcfa.procedures.single().let { procedure ->
      PredicateBlockBehavior(
        xcfa,
        procedure,
        SingleBlockDecomposition.decompose(procedure).blocks.single(),
        roster,
        checkerFallback = checkerFallback,
        cutOnTimeout = cutOnTimeout,
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

  /** Its exit states would be missing from a postcondition that still names its inputs. */
  @Test
  fun `a run without targets that is not safe fails the analysis`() {
    val targetsKept: CheckerFactory = { _ -> cegar(program) }
    val block =
      program.procedures.single().let { procedure ->
        PredicateBlockBehavior(
          program,
          procedure,
          SingleBlockDecomposition.decompose(procedure).blocks.single(),
          DssCheckerRoster(listOf(targetsKept)),
          trackSummaries = true,
        )
      }
    assertThrows(IllegalStateException::class.java) { block.analyzePrecondition() }
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

  /** Queries the deadline for [millis], as a solver-bound analysis does, then runs [then]. */
  private fun busy(millis: Long, then: CheckerFactory? = null): CheckerFactory = { x ->
    SafetyChecker { prec ->
      val end = System.nanoTime() + millis * 1_000_000
      while (System.nanoTime() < end) {
        DssDeadline.check()
        Thread.sleep(5)
      }
      checkNotNull(then) { "this checker never finishes" }(x).check(prec)
    }
  }

  private fun budgeted(checkers: List<CheckerFactory>) =
    DssCheckerRoster(checkers, PriorityCheckerSelectionStrategy(), budgetMs = 50)

  /** Stuck in one solver query until interrupted; [masking] hides the interruption's exception. */
  private fun hung(masking: Boolean): CheckerFactory = { _ ->
    SafetyChecker { _ ->
      val solver = DeadlineSolverFactory(HangingSolverFactory).createSolver()
      try {
        solver.check()
      } catch (e: Exception) {
        if (masking) throw IllegalStateException("the checker gave up") else throw e
      }
      error("an interrupted query cannot answer")
    }
  }

  @Test
  fun `with a budget a checker stuck in one solver query is interrupted for the next one`() {
    for (masking in listOf(false, true)) {
      val used = mutableListOf<String>()
      val checkers = listOf(recording("hung", used, hung(masking)), recording("cegar", used, cegar))
      val messages = initialMessages(checkers, checkerFallback = false, roster = budgeted(checkers))
      assertEquals(listOf(DssMessageType.VIOLATION_CONDITION), messages.map { it.type })
      assertEquals(listOf("hung", "cegar"), used)
    }
  }

  @Test
  fun `with a budget a checker that overruns it gives the turn to the next one`() {
    val used = mutableListOf<String>()
    val checkers = listOf(recording("stuck", used, busy(10_000)), recording("cegar", used, cegar))
    val messages = initialMessages(checkers, checkerFallback = false, roster = budgeted(checkers))
    assertEquals(listOf(DssMessageType.VIOLATION_CONDITION), messages.map { it.type })
    assertEquals(listOf("stuck", "cegar"), used)
  }

  @Test
  fun `with a budget every checker is retried with a growing budget until one finishes`() {
    val used = mutableListOf<String>()
    val checkers =
      listOf(recording("slow", used, busy(120, cegar)), recording("stuck", used, busy(10_000)))
    val messages = initialMessages(checkers, checkerFallback = false, roster = budgeted(checkers))
    assertEquals(listOf(DssMessageType.VIOLATION_CONDITION), messages.map { it.type })
    assertEquals(listOf("slow", "stuck", "slow"), used)
  }

  @Test
  fun `cutting on timeout, a round that every checker runs out of asks for the block to be cut`() {
    for (first in listOf(busy(10_000), crashing)) {
      val used = mutableListOf<String>()
      val checkers = listOf(recording("first", used, first), recording("stuck", used, busy(10_000)))
      val block =
        behavior(checkers, checkerFallback = false, budgeted(checkers), cutOnTimeout = true)
      val e = assertThrows(DssBlockCutRequest::class.java) { block.initialMessages() }
      assertEquals("SB1", e.blockId)
      assertEquals(listOf("first", "stuck"), used)
    }
  }

  @Test
  fun `cutting on timeout, a block without a cut gets a growing budget instead`() {
    val used = mutableListOf<String>()
    val checkers =
      listOf(recording("slow", used, busy(120, cegar)), recording("stuck", used, busy(10_000)))
    val block =
      behavior(checkers, false, budgeted(checkers), cutOnTimeout = true, xcfa = uncuttable)
    assertEquals(
      listOf(DssMessageType.VIOLATION_CONDITION),
      block.initialMessages().map { it.type },
    )
    assertEquals(listOf("slow", "stuck", "slow"), used)
  }

  @Test
  fun `with a budget the checker that finished the last analysis starts the next one`() {
    val used = mutableListOf<String>()
    val checkers = listOf(recording("stuck", used, busy(10_000)), recording("cegar", used, cegar))
    val block = behavior(checkers, checkerFallback = false, roster = budgeted(checkers))
    repeat(2) { block.runInitialAnalysis() }
    assertEquals(listOf("stuck", "cegar", "cegar"), used)
  }

  @Test
  fun `with a budget a crashing checker is dropped and the crash ends the analysis`() {
    val checkers = listOf(crashing, crashing)
    val e =
      assertThrows(SolverBroke::class.java) {
        initialMessages(checkers, checkerFallback = false, roster = budgeted(checkers))
      }
    assertEquals(1, e.suppressed.size)
  }

  @Test
  fun `the finisher analyzes only finishing blocks`() {
    val procedure = program.procedures.single()
    val block = SingleBlockDecomposition.decompose(procedure).blocks.single()
    fun checkersUsed(finishing: Boolean): List<String> {
      val used = mutableListOf<String>()
      val checkers = listOf(recording("cegar", used, cegar), recording("finisher", used, cegar))
      val roster = DssCheckerRoster(checkers, FinisherCheckerSelectionStrategy())
      PredicateBlockBehavior(program, procedure, block, roster, finishing = finishing)
        .initialMessages()
      return used
    }
    assertEquals(listOf("finisher"), checkersUsed(finishing = true))
    assertEquals(listOf("cegar"), checkersUsed(finishing = false))
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
