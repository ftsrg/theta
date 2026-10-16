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
package hu.bme.mit.theta.xcfa.dss.decomposition

import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class MergeBlockDecompositionTest {

  /** root -> three parallel arms, all rejoining at "join" -> final: 5 blocks under `blk_linear`. */
  private fun threeWayBranchJoinProcedure(): XcfaProcedure =
    xcfa("three-way-branch-join") {
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign "0" }
          ("branch" to "arm1") { assume("(= x 0)") }
          ("branch" to "arm2") { assume("(= x 1)") }
          ("branch" to "arm3") { assume("(= x 2)") }
          ("arm1" to "join") { nop() }
          ("arm2" to "join") { nop() }
          ("arm3" to "join") { nop() }
          ("join" to final) { nop() }
        }
      }
      .procedures
      .single()

  @Test
  fun `merges all three structurally parallel arms into one block, at or below the target`() {
    val procedure = threeWayBranchJoinProcedure()
    val baseline = LinearBlockDecomposition().decompose(procedure)
    assertEquals(5, baseline.blocks.size)

    val merged = MergeBlockDecomposition(targetBlockCount = 3).decompose(procedure)

    merged.checkConsistency()
    assertTrue(merged.blocks.size <= 3, "expected at most 3 blocks, got ${merged.blocks.size}")
    val armGroup = merged.blocks.filter { it.locations.any { loc -> loc.name.startsWith("arm") } }
    assertEquals(1, armGroup.size, "all three arms should have collapsed into a single block")
    assertEquals(
      setOf("arm1", "arm2", "arm3"),
      armGroup.single().locations.map { it.name }.filter { it.startsWith("arm") }.toSet(),
    )
  }

  @Test
  fun `a target of 1 collapses everything that can possibly collapse, without hanging`() {
    val procedure = threeWayBranchJoinProcedure()

    val merged = MergeBlockDecomposition(targetBlockCount = 1).decompose(procedure)

    merged.checkConsistency()
    // Every block here sits on a single unbranched path once the three arms are fused together
    // (root -> merged-arms -> tail), so the whole thing can genuinely collapse to one block.
    assertEquals(1, merged.blocks.size)
    assertEquals(procedure.initLoc, merged.root.initialLocation)
    assertTrue(merged.root.finalLocation.final)
  }

  @Test
  fun `a target the graph cannot reach still terminates and stays consistent`() {
    // Two genuinely divergent, non-rejoining arms (one reaches final, the other err) can never be
    // horizontally merged (different finalLocation) or vertically merged (branch has two
    // successors), so no target below 3 is reachable here - mergeToTargetBlockCount must still
    // terminate via its own fixpoint check rather than looping forever chasing an unreachable goal.
    val procedure =
      xcfa("unmergeable-branch") {
          procedure("main") {
            "x" type Int()
            (init to "branch") { "x" assign "0" }
            ("branch" to final) { assume("(< x 10)") }
            ("branch" to err) { assume("(>= x 10)") }
          }
        }
        .procedures
        .single()

    val merged = MergeBlockDecomposition(targetBlockCount = 1).decompose(procedure)

    merged.checkConsistency()
    assertEquals(3, merged.blocks.size, "root + two genuinely divergent dead-end arms")
  }

  @Test
  fun `largestHorizontalMerge is honored end to end`() {
    val procedure = threeWayBranchJoinProcedure()

    val merged =
      MergeBlockDecomposition(targetBlockCount = 1, largestHorizontalMerge = 2).decompose(procedure)

    merged.checkConsistency()
    // Every arm has more locations than the limit, so horizontal merging must never touch them,
    // regardless of how aggressively the target asks to shrink the graph.
    val armBlocks = merged.blocks.filter { it.locations.any { loc -> loc.name.startsWith("arm") } }
    assertEquals(3, armBlocks.size)
  }
}
