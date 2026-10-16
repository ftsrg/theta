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
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** CPAchecker's `NO_DECOMPOSITION` and the single-block corner cases of merging/instrumentation. */
class SingleBlockDecompositionTest {

  private fun loopWithError(): XcfaProcedure =
    xcfa("single") {
        procedure("main") {
          "x" type Int()
          (init to "head") { "x" assign "0" }
          ("head" to "head") { "x" assign "(+ x 1)" }
          ("head" to "check") { assume("(>= x 3)") }
          ("check" to final) { assume("(= x 3)") }
          ("check" to err) { assume("(/= x 3)") }
        }
      }
      .procedures
      .single()

  @Test
  fun `the single block SB1 covers the whole procedure`() {
    val procedure = loopWithError()

    val graph = SingleBlockDecomposition.decompose(procedure)

    graph.checkConsistency()
    val block = graph.blocks.single()
    assertEquals("SB1", block.id)
    assertSame(graph.root, block)
    assertEquals(procedure.initLoc, block.initialLocation)
    assertEquals(procedure.edges, block.edges)
    assertEquals(procedure.locs, block.locations)
    assertTrue(block.finalLocation.outgoingEdges.isEmpty())
    assertTrue(block.predecessorIds.isEmpty() && block.successorIds.isEmpty())
  }

  @Test
  fun `merging to one block may produce the single block directly, if allowed`() {
    val procedure = loopWithError()

    val allowed =
      MergeBlockDecomposition(targetBlockCount = 1, allowSingleBlockDecomposition = true)
        .decompose(procedure)
    val notAllowed = MergeBlockDecomposition(targetBlockCount = 1).decompose(procedure)

    assertEquals(listOf("SB1"), allowed.blocks.map { it.id })
    assertTrue(notAllowed.blocks.size > 1, "a loop cannot be merged away")
  }

  @Test
  fun `the default merge target is CPAchecker's hardcoded 2`() {
    assertEquals(2, DEFAULT_TARGET_BLOCK_COUNT)
  }

  @Test
  fun `instrumenting a single-block graph changes nothing`() {
    val procedure = loopWithError()
    val graph = SingleBlockDecomposition.decompose(procedure)

    val modification = BlockGraphInstrumentation.instrumentForAbstraction(procedure, graph)

    assertSame(procedure, modification.procedure)
    assertSame(graph, modification.blockGraph)
    assertTrue(
      procedure.locs.none { loc -> loc.outgoingEdges.any { it.metadata == GhostEdgeMetadata } }
    )
  }
}
