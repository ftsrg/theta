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
import hu.bme.mit.theta.xcfa.dss.analysis.hasInternalCycle
import hu.bme.mit.theta.xcfa.dss.analysis.runWorkerConfig
import hu.bme.mit.theta.xcfa.dss.decomposition.AcyclicMergeDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.dss.decomposition.CutLoopHandling
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.MergeBlockDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.MinCutDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.SelfLoopAbsorbingDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.getStatistics
import hu.bme.mit.theta.xcfa.dss.decomposition.horizontalMergePass
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test

class MergeDecompositionActorTest {

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

  private fun checkDecomposed(wholeProgram: XCFA, blockGraph: BlockGraph): DssResult {
    val procedure = wholeProgram.procedures.single()
    val checkerRoster = DssCheckerRoster(listOf { x -> cegarChecker(x) })
    return assertTimeoutPreemptively<DssResult>(END_TO_END_TIMEOUT) {
      runDssActorsSequentially(
        blockGraph,
        behaviorFor = { block ->
          PredicateBlockBehavior(wholeProgram, procedure, block, checkerRoster)
        },
      )
    }
  }

  private fun threeWayJoinXcfa(errorValue: Int?): XCFA =
    xcfa("three-way-join-merge") {
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

  private fun mergedBlockGraph(wholeProgram: XCFA, targetBlockCount: Int): BlockGraph {
    val procedure = wholeProgram.procedures.single()
    val linearCount = LinearBlockDecomposition().decompose(procedure).blocks.size
    val merged = MergeBlockDecomposition(targetBlockCount).decompose(procedure)
    merged.checkConsistency()
    assertTrue(merged.blocks.size < linearCount) {
      "expected merging to actually reduce the block count below the unmerged $linearCount, " +
        "got ${merged.blocks.size}"
    }
    return merged
  }

  @Test
  fun `merging actually folds the three parallel arms into one block, not just any three blocks`() {
    val wholeProgram = threeWayJoinXcfa(errorValue = null)
    val procedure = wholeProgram.procedures.single()
    val linear = LinearBlockDecomposition().decompose(procedure)

    val armBlocksBefore = linear.blocks.filter { it.finalLocation.name == "join" }
    assertEquals(3, armBlocksBefore.size) {
      "sanity check: three separate arm blocks before merging"
    }

    val merged = horizontalMergePass(linear)
    merged.checkConsistency()

    val armBlocksAfter = merged.blocks.filter { it.finalLocation.name == "join" }
    assertEquals(1, armBlocksAfter.size) { "the three arms should have folded into one block" }
    assertEquals(
      armBlocksBefore.flatMap { it.locations }.map { it.name }.toSet(),
      armBlocksAfter.single().locations.map { it.name }.toSet(),
    )
  }

  @Test
  fun `a horizontally-merged three-way join reproduces the SAFE verdict through real CEGAR`() {
    val wholeProgram = threeWayJoinXcfa(errorValue = null)
    val blockGraph = mergedBlockGraph(wholeProgram, targetBlockCount = 4)
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram, blockGraph))
    assertTrue(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `a horizontally-merged three-way join reproduces the UNSAFE verdict through real CEGAR`() {
    val wholeProgram = threeWayJoinXcfa(errorValue = 15)
    val blockGraph = mergedBlockGraph(wholeProgram, targetBlockCount = 4)
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram, blockGraph))
    assertTrue(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  private fun xyLoopXcfa(incrementY: Boolean): XCFA =
    xcfa("xy-loop-merge") {
      val main =
        procedure("main") {
          "x" type Int()
          "y" type Int()
          "flag" type Int()
          (init to "loophead") {
            "x" assign "0"
            "y" assign "0"
          }
          ("loophead" to "body") {
            assume("(< x 10)")
            havoc("flag")
          }
          ("loophead" to "afterloop") { assume("(>= x 10)") }
          ("body" to "bodyA") { assume("(= flag 0)") }
          ("body" to "bodyB") { assume("(/= flag 0)") }
          if (incrementY) {
            ("bodyA" to "bodyJoin") {
              "x" assign "(+ x 1)"
              "y" assign "(+ y 1)"
            }
            ("bodyB" to "bodyJoin") {
              "x" assign "(+ x 1)"
              "y" assign "(+ y 1)"
            }
          } else {
            ("bodyA" to "bodyJoin") { "x" assign "(+ x 1)" }
            ("bodyB" to "bodyJoin") { "x" assign "(+ x 1)" }
          }
          ("bodyJoin" to "loophead") { nop() }
          ("afterloop" to final) { assume("(= x y)") }
          ("afterloop" to err) { assume("(/= x y)") }
        }
      main.start()
    }

  @Test
  fun `a merged cyclic block graph reproduces the SAFE verdict`() {
    val wholeProgram = xyLoopXcfa(incrementY = true)
    val blockGraph = mergedBlockGraph(wholeProgram, targetBlockCount = 2)
    assertEquals(DssResult.SAFE, checkDecomposed(wholeProgram, blockGraph))
    assertTrue(checkDirectly(wholeProgram).isSafe) { "test fixture itself should be safe" }
  }

  @Test
  fun `a merged cyclic block graph reproduces the UNSAFE verdict`() {
    val wholeProgram = xyLoopXcfa(incrementY = false)
    val blockGraph = mergedBlockGraph(wholeProgram, targetBlockCount = 2)
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram, blockGraph))
    assertTrue(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
  }

  private fun statefulCheckXcfa(): XCFA =
    xcfa("stateful-check") {
      val main =
        procedure("main") {
          "m" type Int()
          "oc" type Int()
          "s" type Int()
          "c" type Int()
          "r" type Int()
          (init to "loop") {
            "m" assign "1"
            "oc" assign "0"
            "s" assign "0"
          }
          ("loop" to "pick") { havoc("c") }
          ("loop" to "end") { nop() }
          ("pick" to "loop") {
            assume(
              "(not (or (and (= c 0) (= s 0)) (and (= c 1) (= s 1)) (and (= c 2) (= s 2)) " +
                "(and (= c 3) (= s 3))))"
            )
          }
          ("pick" to "open") {
            assume("(and (= c 0) (= s 0))")
            havoc("r")
          }
          ("open" to "loop") {
            assume("(= r 0)")
            "oc" assign "1"
            "s" assign "(+ s 1)"
          }
          ("open" to "loop") {
            assume("(not (= r 0))")
            "s" assign "(+ s 1)"
          }
          ("pick" to "loop") {
            assume("(and (= c 1) (= s 1))")
            "s" assign "(+ s 1)"
          }
          ("pick" to "loop") {
            assume("(and (= c 2) (= s 2))")
            "s" assign "(+ s 1)"
          }
          ("pick" to "release") { assume("(and (= c 3) (= s 3))") }
          ("release" to "lockA") { assume("(not (= oc 0))") }
          ("lockA" to err) { assume("(not (= m 1))") }
          ("lockA" to "unlockA") {
            assume("(= m 1)")
            "m" assign "2"
          }
          ("unlockA" to err) { assume("(not (= m 2))") }
          ("unlockA" to "loop") {
            assume("(= m 2)")
            "m" assign "1"
            "oc" assign "0"
            "s" assign "0"
          }
          ("release" to "lockB") { assume("(= oc 0)") }
          ("lockB" to err) { assume("(not (= m 1))") }
          ("lockB" to "lockB2") {
            assume("(= m 1)")
            "m" assign "2"
          }
          ("lockB2" to err) { assume("(not (= m 1))") }
          ("lockB2" to "loop") {
            assume("(= m 1)")
            "m" assign "2"
            "s" assign "0"
          }
          ("end" to err) { assume("(not (= m 1))") }
          ("end" to final) { assume("(= m 1)") }
        }
      main.start()
    }

  private fun selfLoopAbsorbedBlockGraph(wholeProgram: XCFA): BlockGraph {
    val blockGraph =
      SelfLoopAbsorbingDecomposition().decompose(wholeProgram.procedures.single()).also {
        it.checkConsistency()
      }
    assertTrue(blockGraph.blocks.none { it.id in it.successorIds }) { "no self loop expected" }
    return blockGraph
  }

  @Test
  fun `absorbing the self loop keeps the SAFE and UNSAFE verdicts of the xy loop`() {
    val safeProgram = xyLoopXcfa(incrementY = true)
    val unsafeProgram = xyLoopXcfa(incrementY = false)
    assertEquals(
      DssResult.SAFE,
      checkDecomposed(safeProgram, selfLoopAbsorbedBlockGraph(safeProgram)),
    )
    assertEquals(
      DssResult.UNSAFE,
      checkDecomposed(unsafeProgram, selfLoopAbsorbedBlockGraph(unsafeProgram)),
    )
  }

  private fun guardedLoopXcfa(unsafe: Boolean): XCFA =
    xcfa("guarded-loop") {
      val main =
        procedure("main") {
          "x" type Int()
          "n" type Int()
          (init to "branch") {
            "x" assign "0"
            havoc("n")
          }
          ("branch" to final) { assume("(< n 0)") }
          ("branch" to "loophead") { assume("(>= n 0)") }
          ("loophead" to "body") { assume("(< x n)") }
          ("body" to "loophead") { "x" assign "(+ x 1)" }
          ("loophead" to "afterloop") { assume("(>= x n)") }
          val errorCondition = if (unsafe) "(= x 3)" else "(/= x n)"
          ("afterloop" to final) { assume("(not $errorCondition)") }
          ("afterloop" to err) { assume(errorCondition) }
        }
      main.start()
    }

  @Test
  fun `a non-root block absorbing a loop sends per-path violation conditions to the root`() {
    for (unsafe in listOf(true, false)) {
      val wholeProgram = guardedLoopXcfa(unsafe)
      val blockGraph = selfLoopAbsorbedBlockGraph(wholeProgram)
      val loopBlock = blockGraph.blocks.single { it.locations.any { loc -> loc.name == "body" } }
      assertTrue(hasInternalCycle(loopBlock) && !loopBlock.isRoot) { "fixture shape: $blockGraph" }
      assertEquals(unsafe, checkDirectly(wholeProgram).isUnsafe) { "test fixture itself" }

      assertEquals(
        if (unsafe) DssResult.UNSAFE else DssResult.SAFE,
        checkDecomposed(wholeProgram, blockGraph),
      )
    }
  }

  private fun acyclicBlockGraph(wholeProgram: XCFA): BlockGraph =
    AcyclicMergeDecomposition().decompose(wholeProgram.procedures.single()).also {
      it.checkConsistency()
      assertEquals(0, it.getStatistics().cyclicSccs) { "acyclic block graph expected" }
    }

  private fun errorInGuardedLoopXcfa(bad: String): XCFA =
    xcfa("error-in-guarded-loop") {
      val main =
        procedure("main") {
          "x" type Int()
          "n" type Int()
          (init to "branch") {
            "x" assign "0"
            havoc("n")
          }
          ("branch" to final) { assume("(< n 0)") }
          ("branch" to "loophead") { assume("(>= n 0)") }
          ("loophead" to "check") {
            assume("(< x n)")
            "x" assign "(+ x 1)"
          }
          ("check" to err) { assume("(= x $bad)") }
          ("check" to "loophead") { assume("(/= x $bad)") }
          ("loophead" to final) { assume("(>= x n)") }
        }
      main.start()
    }

  @Test
  fun `an acyclic block graph keeps the verdicts of loops with an error inside`() {
    for ((bad, unsafe) in listOf("3" to true, "(- 0 1)" to false)) {
      val wholeProgram = errorInGuardedLoopXcfa(bad)
      assertEquals(unsafe, checkDirectly(wholeProgram).isUnsafe) { "test fixture itself" }
      assertEquals(
        if (unsafe) DssResult.UNSAFE else DssResult.SAFE,
        checkDecomposed(wholeProgram, acyclicBlockGraph(wholeProgram)),
      )
    }
  }

  @Test
  fun `an acyclic block graph keeps the verdicts of the xy, guarded and stateful loops`() {
    val cases =
      listOf(
        xyLoopXcfa(incrementY = true) to DssResult.SAFE,
        xyLoopXcfa(incrementY = false) to DssResult.UNSAFE,
        guardedLoopXcfa(unsafe = false) to DssResult.SAFE,
        guardedLoopXcfa(unsafe = true) to DssResult.UNSAFE,
        statefulCheckXcfa() to DssResult.UNSAFE,
      )
    for ((wholeProgram, expected) in cases) {
      assertEquals(expected, checkDecomposed(wholeProgram, acyclicBlockGraph(wholeProgram)))
    }
  }

  @Test
  fun `every min-cut version keeps the verdicts of the loop fixtures`() {
    val cases =
      listOf(
        xyLoopXcfa(incrementY = true) to DssResult.SAFE,
        xyLoopXcfa(incrementY = false) to DssResult.UNSAFE,
        guardedLoopXcfa(unsafe = false) to DssResult.SAFE,
        guardedLoopXcfa(unsafe = true) to DssResult.UNSAFE,
        errorInGuardedLoopXcfa("(- 0 1)") to DssResult.SAFE,
        errorInGuardedLoopXcfa("3") to DssResult.UNSAFE,
        statefulCheckXcfa() to DssResult.UNSAFE,
      )
    for (handling in CutLoopHandling.entries) {
      for ((wholeProgram, expected) in cases) {
        val cut = MinCutDecomposition(loopHandling = handling).cut(wholeProgram.procedures.single())
        cut.blockGraph.checkConsistency()
        assertEquals(expected, checkDecomposed(wholeProgram, cut.blockGraph)) {
          "$handling on ${wholeProgram.name}: ${cut.describe().first()}"
        }
      }
    }
  }

  @Test
  fun `absorbing self loops keeps the UNSAFE verdict of a violation four iterations deep`() {
    val wholeProgram = statefulCheckXcfa()
    assertEquals(
      DssResult.UNSAFE,
      checkDecomposed(wholeProgram, selfLoopAbsorbedBlockGraph(wholeProgram)),
    )
  }

  @Test
  fun `a violation four loop iterations deep is UNSAFE with the global predicate pool`() {
    val wholeProgram = statefulCheckXcfa()
    assertTrue(checkDirectly(wholeProgram).isUnsafe) { "test fixture itself should be unsafe" }
    assertEquals(DssResult.UNSAFE, checkDecomposed(wholeProgram, mergedBlockGraph(wholeProgram, 2)))
  }
}
