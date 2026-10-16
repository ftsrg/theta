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

class BlockGraphMergingTest {

  private fun loc(name: String) = XcfaLocation(name, metadata = EmptyMetaData)

  private fun branchJoinProcedure(): XcfaProcedure =
    xcfa("branch-join") {
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign "0" }
          ("branch" to "armA") { assume("(< x 10)") }
          ("branch" to "armB") { assume("(>= x 10)") }
          ("armA" to "join") { "x" assign "(+ x 1)" }
          ("armB" to "join") { "x" assign "(+ x 2)" }
          ("join" to final) { nop() }
        }
      }
      .procedures
      .single()

  @Test
  fun `horizontalMergePass merges two structurally parallel arms into one block`() {
    val procedure = branchJoinProcedure()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)
    assertEquals(4, blockGraph.blocks.size) // root, armA-block, armB-block, tail

    val merged = horizontalMergePass(blockGraph)
    merged.checkConsistency()
    assertEquals(3, merged.blocks.size)

    val mergedArms =
      merged.blocks.single {
        it.locations.map(XcfaLocation::name).containsAll(listOf("armA", "armB"))
      }
    assertEquals(
      setOf("branch", "armA", "armB", "join"),
      mergedArms.locations.map { it.name }.toSet(),
    )
    assertEquals(4, mergedArms.edges.size)
    assertEquals("branch", mergedArms.initialLocation.name)
    assertEquals("join", mergedArms.finalLocation.name)
  }

  @Test
  fun `horizontalMergePass leaves a group of blocks above the size limit unmerged`() {
    val blockGraph = LinearBlockDecomposition().decompose(branchJoinProcedure())

    val result = horizontalMergePass(blockGraph, largestHorizontalMerge = 1)

    result.checkConsistency()
    assertEquals(blockGraph.blocks.map { it.id }.toSet(), result.blocks.map { it.id }.toSet())
  }

  @Test
  fun `horizontalMergePass is a no-op when nothing is structurally parallel`() {
    val procedure =
      xcfa("straight-line") {
          procedure("main") {
            "x" type Int()
            (init to "L0") { "x" assign "0" }
            ("L0" to final) { "x" assign "(+ x 1)" }
          }
        }
        .procedures
        .single()
    val blockGraph = LinearBlockDecomposition().decompose(procedure)

    val result = horizontalMergePass(blockGraph)

    assertEquals(blockGraph.blocks, result.blocks)
  }

  @Test
  fun `verticalMerge collapses a forced straight-line chain down to one block`() {
    val procedure =
      xcfa("straight-line") {
          procedure("main") {
            "x" type Int()
            (init to "L0") { "x" assign "0" }
            ("L0" to "L1") { "x" assign "(+ x 1)" }
            ("L1" to "L2") { "x" assign "(+ x 1)" }
            ("L2" to final) { "x" assign "(+ x 1)" }
          }
        }
        .procedures
        .single()
    // Force every location to be its own block boundary, so this still decomposes into multiple
    // separate blocks for verticalMerge to have something to collapse.
    val blockGraph = LinearBlockDecomposition(isBlockEnd = { true }).decompose(procedure)
    assertTrue(blockGraph.blocks.size > 1)

    val merged = verticalMerge(blockGraph)

    merged.checkConsistency()
    assertEquals(1, merged.blocks.size)
    assertEquals(procedure.initLoc, merged.root.initialLocation)
    assertTrue(merged.root.finalLocation.final)
  }

  @Test
  fun `verticalMerge fuses every unbranched run, including a forcibly-split single arm, but stops exactly at the real join`() {
    val procedure =
      xcfa("branch-join-with-runs") {
          procedure("main") {
            "x" type Int()
            (init to "pre") { nop() }
            ("pre" to "branch") { "x" assign "0" }
            ("branch" to "armA") { assume("(< x 10)") }
            ("branch" to "armB") { assume("(>= x 10)") }
            ("armA" to "join") { "x" assign "(+ x 1)" }
            ("armB" to "join") { "x" assign "(+ x 2)" }
            ("join" to "post") { nop() }
            ("post" to final) { nop() }
          }
        }
        .procedures
        .single()
    // Force every location to be its own block boundary, so this decomposes into one block per
    // edge in the first place, for verticalMerge to have something to collapse - otherwise
    // LinearBlockDecomposition's own snake-collapsing would already have merged most of it.
    val blockGraph = LinearBlockDecomposition(isBlockEnd = { true }).decompose(procedure)
    assertEquals(8, blockGraph.blocks.size)

    val merged = verticalMerge(blockGraph)

    merged.checkConsistency()
    // init->pre and pre->branch fuse; branch->armA and armA->join fuse (armA is not a real branch
    // graph join, so isBlockEnd forcing it to be a location boundary does not stop the block-graph
    // level merge); likewise for armB; join->post and post->final fuse. The genuine join, "join"
    // itself (two block-level predecessors), is exactly where fusing has to stop.
    assertEquals(4, merged.blocks.size)
    val arms =
      merged.blocks.filter {
        it.initialLocation.name == "branch" && it.finalLocation.name == "join"
      }
    assertEquals(
      2,
      arms.size,
      "both arms should have re-fused down to one block each, still separate from each other",
    )
    val beforeBranch = merged.blocks.single { it.finalLocation.name == "branch" }
    val afterJoin = merged.blocks.single { it.initialLocation.name == "join" }
    assertEquals(procedure.initLoc, beforeBranch.initialLocation)
    assertTrue(afterJoin.finalLocation.final)
    for (arm in arms) {
      assertEquals(setOf(beforeBranch.id), arm.predecessorIds)
      assertEquals(setOf(afterJoin.id), arm.successorIds)
    }
    assertEquals(arms.map { it.id }.toSet(), afterJoin.predecessorIds)
  }

  @Test
  fun `alternating vertical then horizontal merge collapses the same graph down to three blocks`() {
    val procedure =
      xcfa("branch-join-with-runs-2") {
          procedure("main") {
            "x" type Int()
            (init to "pre") { nop() }
            ("pre" to "branch") { "x" assign "0" }
            ("branch" to "armA") { assume("(< x 10)") }
            ("branch" to "armB") { assume("(>= x 10)") }
            ("armA" to "join") { "x" assign "(+ x 1)" }
            ("armB" to "join") { "x" assign "(+ x 2)" }
            ("join" to "post") { nop() }
            ("post" to final) { nop() }
          }
        }
        .procedures
        .single()
    val blockGraph = LinearBlockDecomposition(isBlockEnd = { true }).decompose(procedure)

    val merged = horizontalMerge(verticalMerge(blockGraph))

    merged.checkConsistency()
    assertEquals(3, merged.blocks.size)
  }

  @Test
  fun `verticalMerge correctly remaps a hand-built two-block cycle into one self-referencing block`() {
    val r = loc("R")
    val a = loc("A")
    val b = loc("B")
    val root = Block("root", r, r, setOf(r), emptySet(), successorIds = setOf("x"))
    val x =
      Block(
        "x",
        a,
        b,
        setOf(a, b),
        emptySet(),
        predecessorIds = setOf("root", "y"),
        successorIds = setOf("y"),
      )
    val y =
      Block(
        "y",
        b,
        a,
        setOf(a, b),
        emptySet(),
        predecessorIds = setOf("x"),
        successorIds = setOf("x"),
      )
    val blockGraph = BlockGraph(setOf(root, x, y))
    blockGraph.checkConsistency() // the fixture itself must be valid before testing the merge

    val merged = verticalMerge(blockGraph)

    merged.checkConsistency()
    assertEquals(2, merged.blocks.size)
    val combined = merged.blocks.single { it.id != "root" }
    assertTrue(combined.id in combined.predecessorIds, "expected a self-reference, not a stale id")
    assertTrue(combined.id in combined.successorIds, "expected a self-reference, not a stale id")
    assertEquals(setOf("root", combined.id), combined.predecessorIds)
    assertEquals(setOf(combined.id), merged.blocks.single { it.id == "root" }.successorIds)
  }

  private fun chainProcedure(): XcfaProcedure =
    xcfa("chain") {
        procedure("main") {
          "x" type Int()
          (init to "L0") { "x" assign "0" }
          ("L0" to "L1") { "x" assign "(+ x 1)" }
          ("L1" to "L2") { "x" assign "(+ x 1)" }
          ("L2" to final) { "x" assign "(+ x 1)" }
        }
      }
      .procedures
      .single()

  @Test
  fun `blocks are named like CPAchecker's - L for linear, MH and MV for merged blocks`() {
    val linear = LinearBlockDecomposition().decompose(branchJoinProcedure())
    assertEquals(setOf("L0", "L1", "L2", "L3"), linear.blocks.map { it.id }.toSet())

    val horizontal = horizontalMergePass(linear)
    assertTrue(horizontal.blocks.any { it.id == "MH0" }, "${horizontal.blocks.map { it.id }}")

    val vertical = verticalMergePass(horizontal)
    assertTrue(vertical.blocks.any { it.id == "MV0" }, "${vertical.blocks.map { it.id }}")
  }

  @Test
  fun `a single verticalMergePass merges every block at most once, like CPAchecker's`() {
    val blockGraph = LinearBlockDecomposition(isBlockEnd = { true }).decompose(chainProcedure())
    assertEquals(4, blockGraph.blocks.size)

    val onePass = verticalMergePass(blockGraph)

    onePass.checkConsistency()
    // L0+L1 and L2+L3 fuse; the two results only fuse in the next pass.
    assertEquals(setOf("MV0", "MV1"), onePass.blocks.map { it.id }.toSet())
    assertEquals(1, verticalMergePass(onePass).blocks.size)
  }

  @Test
  fun `merge passes stop as soon as the target block count is reached`() {
    val blockGraph = LinearBlockDecomposition(isBlockEnd = { true }).decompose(chainProcedure())

    val merged = verticalMergePass(blockGraph, targetBlockCount = 3)

    merged.checkConsistency()
    assertEquals(3, merged.blocks.size)
  }
}
