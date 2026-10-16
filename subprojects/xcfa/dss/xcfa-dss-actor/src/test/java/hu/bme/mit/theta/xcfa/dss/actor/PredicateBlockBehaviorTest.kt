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
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.runWorkerConfig
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.model.*
import java.time.Duration
import java.util.concurrent.atomic.AtomicIntegerArray
import kotlin.math.abs
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/**
 * Build-order step 5: a multi-block `LINEAR_DECOMPOSITION` program checked through the full actor
 * runtime with [PredicateBlockBehavior] gives the same verdict as the undecomposed program.
 */
class PredicateBlockBehaviorTest {

  companion object {

    @JvmStatic
    @BeforeAll
    fun registerSolvers() {
      ensureDefaultSolversRegistered(getDefaultPredCegarConfig(), NullLogger.getInstance())
    }
  }

  private fun cegarChecker(xcfa: XCFA) =
    getCegarChecker(
      xcfa,
      emptySet(),
      ParseContext(),
      getDefaultPredCegarConfig(),
      NullLogger.getInstance(),
    )

  private fun checkDirectly(xcfa: XCFA) =
    runWorkerConfig(xcfa, checkerFactory = { x -> cegarChecker(x) })

  private fun checkDecomposed(
    wholeProgram: XCFA,
    useGlobalPredicatePool: Boolean = true,
  ): DssResult {
    val procedure = wholeProgram.procedures.single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    // One roster shared by all blocks, as DssCheckerRoster requires; with one checker a per-block
    // roster wouldn't show, but the round-robin distribution test below would catch it.
    val checkerRoster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    // Sequential only: the default (legacy) Z3 is not thread-safe
    return assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(60)) {
      runDssActorsSequentially(
        blockGraph,
        behaviorFor = { block ->
          PredicateBlockBehavior(
            wholeProgram,
            procedure,
            block,
            checkerRoster,
            useGlobalPredicatePool,
          )
        },
      )
    }
  }

  /** init->branch assigns x, then branches on x < 10 vs x >= 10 into a safe/error location. */
  private fun branchingXcfa(assignedValue: String): XCFA =
    xcfa("predicate-block-behavior") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign assignedValue }
          ("branch" to "checkA") { assume("(< x 10)") }
          ("branch" to "checkB") { assume("(>= x 10)") }
          ("checkA" to final) { nop() }
          ("checkB" to err) { nop() }
        }
      main.start()
    }

  @Test
  fun `a decomposed SAFE program reproduces the non-decomposed SAFE verdict`() {
    val wholeProgram = branchingXcfa(assignedValue = "5")
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `a decomposed UNSAFE program reproduces the non-decomposed UNSAFE verdict`() {
    val wholeProgram = branchingXcfa(assignedValue = "20")
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  /**
   * Two branches join before the check, so the join block must accumulate both postconditions:
   * `checkD`/`err` are unreachable from x == 3 alone, but reachable from x == 15.
   */
  private fun joinXcfa(): XCFA =
    xcfa("predicate-block-behavior-join") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "branch") { havoc("y") }
          ("branch" to "pathA") { assume("(< y 0)") }
          ("branch" to "pathB") { assume("(>= y 0)") }
          ("pathA" to "join") { "x" assign "3" }
          ("pathB" to "join") { "x" assign "15" }
          ("join" to "checkC") { assume("(< x 10)") }
          ("join" to "checkD") { assume("(>= x 10)") }
          ("checkC" to final) { nop() }
          ("checkD" to err) { nop() }
        }
      main.start()
    }

  @Test
  fun `a join block accumulates both predecessors before reporting the correct UNSAFE verdict`() {
    val wholeProgram = joinXcfa()
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  /**
   * The default round-robin roster spreads a real multi-recheck run (the join block) across two
   * copies of the same config - testing distribution, not convergence of different checkers.
   */
  @Test
  fun `the default round-robin roster distributes real checks across every checker it's given`() {
    val wholeProgram = joinXcfa()
    val procedure = wholeProgram.procedures.single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val counts = AtomicIntegerArray(2)
    val checkers: List<CheckerFactory> =
      listOf(
        { x: XCFA ->
          counts.incrementAndGet(0)
          cegarChecker(x)
        },
        { x: XCFA ->
          counts.incrementAndGet(1)
          cegarChecker(x)
        },
      )
    val checkerRoster = DssCheckerRoster(checkers)
    val result =
      assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(60)) {
        runDssActorsSequentially(
          blockGraph,
          behaviorFor = { block ->
            PredicateBlockBehavior(wholeProgram, procedure, block, checkerRoster)
          },
        )
      }
    assertEquals(DssResult.UNSAFE, result)
    val (countA, countB) = counts.get(0) to counts.get(1)
    assert(countA > 0 && countB > 0) {
      "expected both checkers in the roster to be used at least once, got ($countA, $countB)"
    }
    assert(abs(countA - countB) <= 1) {
      "expected round-robin usage to differ by at most 1, got ($countA, $countB)"
    }
  }

  /**
   * Without the global predicate pool (empty precision, like CPAchecker), the spurious `err` only
   * yields a violation condition the root refutes by refinement - the pool just saves rounds.
   */
  @Test
  fun `without the global predicate pool, violation conditions still refute the spurious error`() {
    val wholeProgram = branchingXcfa(assignedValue = "5")
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram, useGlobalPredicatePool = true))
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram, useGlobalPredicatePool = false))
    assert(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }
}
