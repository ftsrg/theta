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
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.runWorkerConfig
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.model.*
import java.time.Duration
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/**
 * Build-order step 6: real per-block CEGAR on a cyclic block graph (the paper's `x`/`y` loop body
 * is its own successor), under both [runDssActors] and [runDssActorsSequentially].
 */
class CyclicBlockGraphAnalysisTest {

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
    executor: (BlockGraph, (Block) -> DssBlockBehavior) -> DssResult,
  ): DssResult {
    val procedure = wholeProgram.procedures.single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val checkerRoster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    return assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(60)) {
      executor(blockGraph) { block ->
        PredicateBlockBehavior(wholeProgram, procedure, block, checkerRoster)
      }
    }
  }

  /**
   * The paper's running example: `x`/`y` incremented in a while loop, then `assert(x == y)` - safe
   * iff [incrementY] keeps `y` in lockstep with `x`.
   */
  private fun xyLoopXcfa(incrementY: Boolean): XCFA =
    xcfa("xy-loop") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "loophead") {
            "x" assign "0"
            "y" assign "0"
          }
          ("loophead" to "body") { assume("(< x 10)") }
          ("loophead" to "afterloop") { assume("(>= x 10)") }
          if (incrementY) {
            ("body" to "loophead") {
              "x" assign "(+ x 1)"
              "y" assign "(+ y 1)"
            }
          } else {
            ("body" to "loophead") { "x" assign "(+ x 1)" }
          }
          ("afterloop" to final) { assume("(= x y)") }
          ("afterloop" to err) { assume("(/= x y)") }
        }
      main.start()
    }

  @Test
  fun `sequential executor reproduces the SAFE verdict through a cyclic block graph`() {
    val wholeProgram = xyLoopXcfa(incrementY = true)
    assertEquals(
      DssResult.SAFE,
      checkDecomposed(wholeProgram) { bg, bf -> runDssActorsSequentially(bg, bf) },
    )
    assert(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `sequential executor reproduces the UNSAFE verdict through a cyclic block graph`() {
    val wholeProgram = xyLoopXcfa(incrementY = false)
    assertEquals(
      DssResult.UNSAFE,
      checkDecomposed(wholeProgram) { bg, bf -> runDssActorsSequentially(bg, bf) },
    )
    assert(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  @Test
  fun `concurrent executor reproduces the SAFE verdict through a cyclic block graph`() {
    val wholeProgram = xyLoopXcfa(incrementY = true)
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram) { bg, bf -> runDssActors(bg, bf) })
  }

  @Test
  fun `concurrent executor reproduces the UNSAFE verdict through a cyclic block graph`() {
    val wholeProgram = xyLoopXcfa(incrementY = false)
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram) { bg, bf -> runDssActors(bg, bf) })
  }
}
