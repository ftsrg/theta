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

class AcyclicMergeDecompositionTest {

  private fun loc(name: String) = XcfaLocation(name, metadata = EmptyMetaData)

  private fun BlockGraph.assertAcyclicCover(procedure: XcfaProcedure) {
    checkConsistency()
    assertEquals(0, statistics().cyclicSccs, "cyclic block graph: ${blocks.map { it.id }}")
    assertEquals(procedure.edges, blocks.flatMap { it.edges }.toSet())
  }

  private fun XcfaProcedure.decomposedWith(decomposition: DssBlockDecomposition) =
    decomposition.decompose(this)

  /**
   * while (x < 10) { x++; if (x == 7) error; } - the error splits the loop into a 2-block cycle.
   */
  private fun errorInLoopProcedure(): XcfaProcedure =
    xcfa("error-in-loop") {
        procedure("main") {
          "x" type Int()
          (init to "loophead") { "x" assign "0" }
          ("loophead" to "check") {
            assume("(< x 10)")
            "x" assign "(+ x 1)"
          }
          ("check" to err) { assume("(= x 7)") }
          ("check" to "loophead") { assume("(/= x 7)") }
          ("loophead" to final) { assume("(>= x 10)") }
        }
      }
      .procedures
      .single()

  /** while (x < 10) { if (y) break; x++; } after; - two exits that rejoin after the loop. */
  private fun breakProcedure(): XcfaProcedure =
    xcfa("break") {
        procedure("main") {
          "x" type Int()
          "y" type Int()
          (init to "loophead") {
            "x" assign "0"
            havoc("y")
          }
          ("loophead" to "body") { assume("(< x 10)") }
          ("body" to "after") { assume("(/= y 0)") }
          ("body" to "loophead") {
            assume("(= y 0)")
            "x" assign "(+ x 1)"
          }
          ("loophead" to "after") { assume("(>= x 10)") }
          ("after" to final) { assume("(<= x 10)") }
          ("after" to err) { assume("(> x 10)") }
        }
      }
      .procedures
      .single()

  /** Nested loops whose inner body branches on the error, so neither loop is a single block. */
  private fun nestedProcedure(): XcfaProcedure =
    xcfa("nested") {
        procedure("main") {
          "i" type Int()
          "j" type Int()
          (init to "outer") { "i" assign "0" }
          ("outer" to "inner") {
            assume("(< i 3)")
            "j" assign "0"
          }
          ("inner" to "innerCheck") {
            assume("(< j 2)")
            "j" assign "(+ j 1)"
          }
          ("innerCheck" to err) { assume("(> j 2)") }
          ("innerCheck" to "inner") { assume("(<= j 2)") }
          ("inner" to "outer") {
            assume("(>= j 2)")
            "i" assign "(+ i 1)"
          }
          ("outer" to final) { assume("(>= i 3)") }
        }
      }
      .procedures
      .single()

  @Test
  fun `a cycle through two blocks with an exit in the middle becomes one block`() {
    val procedure = errorInLoopProcedure()
    val selfLoopsOnly = procedure.decomposedWith(SelfLoopAbsorbingDecomposition())
    assertTrue(selfLoopsOnly.statistics().cyclicSccs > 0, "sanity check: not a self loop")

    val acyclic = procedure.decomposedWith(AcyclicMergeDecomposition())

    acyclic.assertAcyclicCover(procedure)
    val loopBlock = acyclic.blocks.single { block -> block.locations.any { it.name == "check" } }
    assertTrue(loopBlock.locations.any { it.error }, "the error exit is inside the loop block")
  }

  @Test
  fun `a loop with a break grows to the location where both exits rejoin`() {
    val procedure = breakProcedure()
    assertTrue(procedure.decomposedWith(MergeBlockDecomposition()).statistics().cyclicSccs > 0)

    val acyclic = procedure.decomposedWith(AcyclicMergeDecomposition())

    acyclic.assertAcyclicCover(procedure)
    assertTrue(acyclic.blocks.none { it.initialLocation.name == "loophead" })
  }

  @Test
  fun `nested cycles collapse until the graph is acyclic`() {
    val procedure = nestedProcedure()
    assertTrue(procedure.decomposedWith(MergeBlockDecomposition()).statistics().cyclicSccs > 0)

    procedure.decomposedWith(AcyclicMergeDecomposition()).assertAcyclicCover(procedure)
  }

  @Test
  fun `no merged block starts and ends at the same location`() {
    for (procedure in listOf(errorInLoopProcedure(), breakProcedure(), nestedProcedure())) {
      val acyclic = procedure.decomposedWith(AcyclicMergeDecomposition())
      assertTrue(acyclic.blocks.none { it.initialLocation == it.finalLocation })
    }
  }

  @Test
  fun `an acyclic graph is returned as it is`() {
    val (a, b, c) = listOf(loc("A"), loc("B"), loc("C"))
    val graph =
      BlockGraph.fromBlocksWithoutEdges(
        listOf(Block("r", a, b, setOf(a, b), emptySet()), Block("s", b, c, setOf(b, c), emptySet()))
      )
    assertSame(graph, collapseCycles(graph))
  }

  @Test
  fun `a cycle entered and left at the same location grows over its predecessors`() {
    // r: A->B, p: B->C, z: B->D, w: D->C, c1: C->E, c2: E->C, x: C->F
    val (a, b, c, d) = listOf(loc("A"), loc("B"), loc("C"), loc("D"))
    val (e, f) = listOf(loc("E"), loc("F"))
    val graph =
      BlockGraph.fromBlocksWithoutEdges(
        listOf(
          Block("r", a, b, setOf(a, b), emptySet()),
          Block("p", b, c, setOf(b, c), emptySet()),
          Block("z", b, d, setOf(b, d), emptySet()),
          Block("w", d, c, setOf(d, c), emptySet()),
          Block("c1", c, e, setOf(c, e), emptySet()),
          Block("c2", e, c, setOf(e, c), emptySet()),
          Block("x", c, f, setOf(c, f), emptySet()),
        )
      )

    val acyclic = collapseCycles(graph)

    // entry = exit = C adds p and w, whose two entries B and D add r and z
    acyclic.checkConsistency()
    assertEquals(0, acyclic.statistics().cyclicSccs)
    assertEquals(setOf("MC0", "x"), acyclic.blocks.map { it.id }.toSet())
    val merged = acyclic.blocks.single { it.id == "MC0" }
    assertEquals(listOf("A", "C"), listOf(merged.initialLocation.name, merged.finalLocation.name))
  }
}
