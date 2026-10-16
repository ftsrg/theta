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
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

/**
 * More diverse programs through real per-block CEGAR, each checked against the undecomposed
 * baseline: a three-way join, nested branches, a loop with a break, and two sequential loops.
 */
class DiverseProgramsActorTest {

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

  private fun checkDecomposed(wholeProgram: XCFA): DssResult {
    val procedure = wholeProgram.procedures.single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    val checkerRoster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    // Sequential only: the default (legacy) Z3 is not thread-safe
    return assertTimeoutPreemptively<DssResult>(END_TO_END_TIMEOUT) {
      runDssActorsSequentially(
        blockGraph,
        behaviorFor = { block ->
          PredicateBlockBehavior(wholeProgram, procedure, block, checkerRoster)
        },
      )
    }
  }

  /**
   * `branch` splits three ways, each arm assigning a distinct `x` before rejoining at `join` -
   * three predecessors accumulating into one block.
   */
  private fun threeWayJoinXcfa(errorValue: Int?): XCFA =
    xcfa("three-way-join") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "branch") { havoc("y") }
          ("branch" to "arm1") { assume("(< y 0)") }
          ("branch" to "arm2") { assume("(= y 5)") }
          ("branch" to "arm3") { assume("(> y 100)") }
          ("arm1" to "join") { "x" assign "1" }
          ("arm2" to "join") { "x" assign "2" }
          ("arm3" to "join") { "x" assign if (errorValue != null) "$errorValue" else "3" }
          ("join" to "checkSafe") { assume("(< x 10)") }
          ("join" to "checkErr") { assume("(>= x 10)") }
          ("checkSafe" to final) { nop() }
          ("checkErr" to err) { nop() }
        }
      main.start()
    }

  @Test
  fun `a three-way join reproduces the SAFE verdict when every arm is well-behaved`() {
    val wholeProgram = threeWayJoinXcfa(errorValue = null)
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `a three-way join reproduces the UNSAFE verdict when one arm alone is enough to violate it`() {
    val wholeProgram = threeWayJoinXcfa(errorValue = 15)
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  /**
   * A branch inside a branch, all arms rejoining at `join` - a block graph more than one hop deep.
   */
  private fun nestedBranchXcfa(errorValue: Int?): XCFA =
    xcfa("nested-branch") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "outer") { havoc("x") }
          ("outer" to "inner") { assume("(< x 10)") }
          ("outer" to "elseOuter") { assume("(>= x 10)") }
          ("inner" to "innerA") { assume("(< x 0)") }
          ("inner" to "innerB") { assume("(>= x 0)") }
          ("innerA" to "join") { "y" assign "1" }
          ("innerB" to "join") { "y" assign "2" }
          ("elseOuter" to "join") { "y" assign if (errorValue != null) "$errorValue" else "3" }
          ("join" to "checkSafe") { assume("(< y 10)") }
          ("join" to "checkErr") { assume("(>= y 10)") }
          ("checkSafe" to final) { nop() }
          ("checkErr" to err) { nop() }
        }
      main.start()
    }

  @Test
  fun `a nested branch reproduces the SAFE verdict`() {
    val wholeProgram = nestedBranchXcfa(errorValue = null)
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `a nested branch reproduces the UNSAFE verdict when the outer else-arm alone violates it`() {
    val wholeProgram = nestedBranchXcfa(errorValue = 15)
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  /**
   * A loop that breaks early at `x >= 5` or loops back - a two-block cycle under `blk_linear`, not
   * a single self-loop. Every path to `afterloop` guarantees `x >= 5`.
   */
  private fun loopWithBreakXcfa(safe: Boolean): XCFA =
    xcfa("loop-with-break") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "loophead") { "x" assign "0" }
          ("loophead" to "body") { assume("(< x 10)") }
          ("loophead" to "afterloop") { assume("(>= x 10)") }
          ("body" to "checkBreak") { "x" assign "(+ x 1)" }
          ("checkBreak" to "afterloop") { assume("(>= x 5)") }
          ("checkBreak" to "loophead") { assume("(< x 5)") }
          if (safe) {
            ("afterloop" to final) { assume("(< x 100)") }
            ("afterloop" to err) { assume("(>= x 100)") }
          } else {
            ("afterloop" to final) { assume("(< x 5)") }
            ("afterloop" to err) { assume("(>= x 5)") }
          }
        }
      main.start()
    }

  @Test
  fun `a loop with a mid-loop break reproduces the SAFE verdict through a two-block cycle`() {
    val wholeProgram = loopWithBreakXcfa(safe = true)
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `a loop with a mid-loop break reproduces the UNSAFE verdict through a two-block cycle`() {
    val wholeProgram = loopWithBreakXcfa(safe = false)
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  /**
   * Two loops in sequence joined by a straight-line "mid" block - two cyclic components. The final
   * check reuses loop 1's guard (`x >= 5`): Cartesian abstraction can't prove `x == 5` here.
   */
  private fun twoSequentialLoopsXcfa(safe: Boolean): XCFA =
    xcfa("two-sequential-loops") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "loop1head") { "x" assign "0" }
          ("loop1head" to "loop1body") { assume("(< x 5)") }
          ("loop1head" to "mid") { assume("(>= x 5)") }
          ("loop1body" to "loop1head") { "x" assign "(+ x 1)" }
          ("mid" to "loop2head") { "y" assign "0" }
          ("loop2head" to "loop2body") { assume("(< y 5)") }
          ("loop2head" to "afterloop2") { assume("(>= y 5)") }
          ("loop2body" to "loop2head") { "y" assign "(+ y 1)" }
          if (safe) {
            ("afterloop2" to final) { assume("(>= x 5)") }
            ("afterloop2" to err) { assume("(< x 5)") }
          } else {
            ("afterloop2" to final) { assume("(< x 5)") }
            ("afterloop2" to err) { assume("(>= x 5)") }
          }
        }
      main.start()
    }

  @Test
  fun `two independent sequential loops reproduce the SAFE verdict`() {
    val wholeProgram = twoSequentialLoopsXcfa(safe = true)
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `two independent sequential loops reproduce the UNSAFE verdict`() {
    val wholeProgram = twoSequentialLoopsXcfa(safe = false)
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram))
    assert(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }
}
