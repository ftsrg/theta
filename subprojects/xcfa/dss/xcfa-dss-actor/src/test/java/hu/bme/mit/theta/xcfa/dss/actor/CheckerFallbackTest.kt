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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.cli.checkers.getCegarChecker
import hu.bme.mit.theta.xcfa.cli.params.defaultPredicateCegarConfig
import hu.bme.mit.theta.xcfa.cli.utils.ensureDefaultSolversRegistered
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.PriorityCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/**
 * `--dss-checker-fallback`: a block analysis whose checker throws is repeated with the next one.
 */
class CheckerFallbackTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(defaultPredicateCegarConfig(), NullLogger.getInstance())
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
      defaultPredicateCegarConfig(),
      NullLogger.getInstance(),
    )
  }

  private fun initialMessages(
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
        .initialMessages()
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
  fun `the trace shows every try with its outcome`() {
    val lines = mutableListOf<String>()
    DssTrace.enable { lines += it }
    try {
      initialMessages(listOf(crashing, cegar), checkerFallback = true)
    } finally {
      DssTrace.disable()
    }
    val events = lines.map { it.split(' ').drop(2) }
    assertEquals(
      listOf(
        "analysis-start attempt=0",
        "analysis-end attempt=0 outcome=exception:SolverBroke",
        "analysis-start attempt=1",
        "analysis-end attempt=1 outcome=unsafe",
      ),
      events.map { e ->
        (listOf(e.first()) + e.filter { it.startsWith("attempt=") || it.startsWith("outcome=") })
          .joinToString(" ")
      },
    )
    assert(lines.all { "block=" in it && "preds=" in it })
  }
}
