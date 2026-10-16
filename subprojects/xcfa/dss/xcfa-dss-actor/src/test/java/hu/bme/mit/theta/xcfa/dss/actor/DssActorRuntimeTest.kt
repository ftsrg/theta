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

import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.time.Duration
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Test

/**
 * Validates the actor runtime's routing and termination detection against [EchoBlockAnalysis] stub
 * workers, before any real per-block CEGAR is wired in (build-order step 4).
 */
class DssActorRuntimeTest {

  private fun loc(name: String) = XcfaLocation(name, metadata = EmptyMetaData)

  private fun block(
    id: String,
    predecessorIds: Set<String> = emptySet(),
    successorIds: Set<String> = emptySet(),
  ): Block {
    val entry = loc("$id-in")
    val exit = loc("$id-out")
    return Block(id, entry, exit, setOf(entry, exit), emptySet(), predecessorIds, successorIds)
  }

  /** Fails the test instead of hanging forever if the actor network never reaches quiescence. */
  private fun runWithTimeout(
    blockGraph: BlockGraph,
    behaviorFor: (Block) -> DssBlockBehavior,
  ): DssResult =
    assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(10)) {
      runDssActors(blockGraph, behaviorFor)
    }

  @Test
  fun `a straight chain with no violations reports SAFE`() {
    val root = block("R", successorIds = setOf("A"))
    val a = block("A", predecessorIds = setOf("R"), successorIds = setOf("B"))
    val b = block("B", predecessorIds = setOf("A"))
    val blockGraph = BlockGraph(setOf(root, a, b))

    val result = runWithTimeout(blockGraph) { EchoBlockAnalysis(it.id) }

    assertEquals(DssResult.SAFE, result)
  }

  @Test
  fun `a branch that joins back together with no violations reports SAFE`() {
    val root = block("R", successorIds = setOf("A", "B"))
    val a = block("A", predecessorIds = setOf("R"), successorIds = setOf("C"))
    val b = block("B", predecessorIds = setOf("R"), successorIds = setOf("C"))
    val c = block("C", predecessorIds = setOf("A", "B"))
    val blockGraph = BlockGraph(setOf(root, a, b, c))

    val result = runWithTimeout(blockGraph) { EchoBlockAnalysis(it.id) }

    assertEquals(DssResult.SAFE, result)
  }

  @Test
  fun `a cyclic block graph (a loop-body block that is its own predecessor and successor) still reaches SAFE`() {
    // Mirrors xcfa-dss-decomposition's "tight self-loop" case: the loop-head block lists itself as
    // both predecessor and successor. Quiescence detection must handle this without special-casing
    // cycles at all (plan §2's whole point).
    val root = block("R", successorIds = setOf("LH"))
    val loopHead = block("LH", predecessorIds = setOf("R", "LH"), successorIds = setOf("LH", "X"))
    val exit = block("X", predecessorIds = setOf("LH"))
    val blockGraph = BlockGraph(setOf(root, loopHead, exit))

    val result = runWithTimeout(blockGraph) { EchoBlockAnalysis(it.id) }

    assertEquals(DssResult.SAFE, result)
  }

  @Test
  fun `a root block that finds a violation on its own reports UNSAFE immediately`() {
    val root = block("R")
    val blockGraph = BlockGraph(setOf(root))

    val result = runWithTimeout(blockGraph) { EchoBlockAnalysis(it.id, originatesViolation = true) }

    assertEquals(DssResult.UNSAFE, result)
  }

  @Test
  fun `a violation found deep in the block graph propagates back to the root before reporting UNSAFE`() {
    val root = block("R", successorIds = setOf("A"))
    val a = block("A", predecessorIds = setOf("R"), successorIds = setOf("B"))
    val leaf = block("B", predecessorIds = setOf("A"))
    val blockGraph = BlockGraph(setOf(root, a, leaf))

    val result =
      runWithTimeout(blockGraph) { block ->
        EchoBlockAnalysis(block.id, originatesViolation = block.id == "B")
      }

    assertEquals(DssResult.UNSAFE, result)
  }

  @Test
  fun `a violation in one branch of a join reports UNSAFE even though the other branch is clean`() {
    val root = block("R", successorIds = setOf("A", "B"))
    val a = block("A", predecessorIds = setOf("R"), successorIds = setOf("C"))
    val b = block("B", predecessorIds = setOf("R"), successorIds = setOf("C"))
    val c = block("C", predecessorIds = setOf("A", "B"))
    val blockGraph = BlockGraph(setOf(root, a, b, c))

    val result =
      runWithTimeout(blockGraph) { block ->
        EchoBlockAnalysis(block.id, originatesViolation = block.id == "C")
      }

    assertEquals(DssResult.UNSAFE, result)
  }
}
