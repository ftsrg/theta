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
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class BlockGraphInstrumentationTest {

  /** init->branch, branch->thenLoc->final, branch->elseLoc->final: same fixture as step 1. */
  private fun ifElseProcedure() =
    xcfa("if-else") {
        procedure("main") {
          "x" type Int()
          (init to "branch") { "x" assign "0" }
          ("branch" to "thenLoc") { assume("(< x 10)") }
          ("branch" to "elseLoc") { assume("(>= x 10)") }
          ("thenLoc" to final) { "x" assign "(+ x 1)" }
          ("elseLoc" to final) { "x" assign "(+ x 2)" }
        }
      }
      .procedures
      .single()

  @Test
  fun `blocks ending mid-procedure get a dedicated abstraction point`() {
    val procedure = ifElseProcedure()
    val decomposed = LinearBlockDecomposition().decompose(procedure)

    val modification = BlockGraphInstrumentation.instrumentForAbstraction(procedure, decomposed)
    modification.blockGraph.checkConsistency()

    // The root block ends at "branch", which has somewhere to go (two outgoing edges) - it should
    // get a fresh, dedicated abstraction point.
    val root = modification.blockGraph.root
    assertEquals("branch", root.finalLocation.name)
    assertTrue(root.isAbstractionPossible)
    assertNotEquals(root.finalLocation, root.violationConditionLocation)
    assertTrue(root.violationConditionLocation in root.locations)
    assertTrue(root.violationConditionLocation.name.startsWith("branch"))
  }

  @Test
  fun `blocks ending in a genuine dead end get no ghost edge`() {
    val procedure = ifElseProcedure()
    val decomposed = LinearBlockDecomposition().decompose(procedure)

    val modification = BlockGraphInstrumentation.instrumentForAbstraction(procedure, decomposed)

    val armsEndingAtFinal = modification.blockGraph.blocks.filter { it.finalLocation.final }
    assertEquals(2, armsEndingAtFinal.size)
    armsEndingAtFinal.forEach { arm ->
      assertFalse(arm.isAbstractionPossible)
      assertEquals(arm.finalLocation, arm.violationConditionLocation)
    }
  }

  @Test
  fun `instrumentation does not change the block graph's topology`() {
    val procedure = ifElseProcedure()
    val decomposed = LinearBlockDecomposition().decompose(procedure)

    val modification = BlockGraphInstrumentation.instrumentForAbstraction(procedure, decomposed)

    assertEquals(
      decomposed.blocks.map { it.id }.toSet(),
      modification.blockGraph.blocks.map { it.id }.toSet(),
    )
    for (block in decomposed.blocks) {
      val instrumented = modification.blockGraph.blocks.single { it.id == block.id }
      assertEquals(block.initialLocation, instrumented.initialLocation)
      assertEquals(block.finalLocation, instrumented.finalLocation)
      assertEquals(block.predecessorIds, instrumented.predecessorIds)
      assertEquals(block.successorIds, instrumented.successorIds)
    }
  }

  @Test
  fun `the ghost edge is really wired into the procedure's control-flow graph`() {
    val procedure = ifElseProcedure()
    val decomposed = LinearBlockDecomposition().decompose(procedure)

    val modification = BlockGraphInstrumentation.instrumentForAbstraction(procedure, decomposed)

    val root = modification.blockGraph.root
    val ghostLocation = root.violationConditionLocation
    val branchLocation = root.finalLocation

    // The ghost edge is a real outgoing edge of "branch" (alongside the two original ones), not
    // just bookkeeping recorded on the Block.
    val ghostEdge = branchLocation.outgoingEdges.single { it.target == ghostLocation }
    assertTrue(ghostEdge in root.edges)
    assertEquals(GhostEdgeMetadata, ghostEdge.metadata)
    assertEquals(GhostEdgeMetadata, ghostLocation.metadata)
    assertEquals(3, branchLocation.outgoingEdges.size)
    assertTrue(ghostLocation.outgoingEdges.isEmpty())
    assertTrue(ghostLocation in modification.procedure.locs)
    assertTrue(ghostEdge in modification.procedure.edges)
  }

  @Test
  fun `a block that already ended in a dead end keeps its original locations and edges untouched`() {
    val procedure = ifElseProcedure()
    val decomposed = LinearBlockDecomposition().decompose(procedure)
    val armBefore =
      decomposed.blocks.single { block -> block.locations.any { it.name == "thenLoc" } }

    val modification = BlockGraphInstrumentation.instrumentForAbstraction(procedure, decomposed)
    val armAfter = modification.blockGraph.blocks.single { it.id == armBefore.id }

    assertEquals(armBefore.locations, armAfter.locations)
    assertEquals(armBefore.edges, armAfter.edges)
  }
}
