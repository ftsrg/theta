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

class SelfLoopAbsorbingDecompositionTest {

  private fun loc(name: String) = XcfaLocation(name, metadata = EmptyMetaData)

  private fun BlockGraph.selfLoops() = blocks.filter { it.id in it.successorIds }

  private fun BlockGraph.assertCovers(procedure: XcfaProcedure) {
    assertEquals(procedure.edges, blocks.flatMap { it.edges }.toSet())
    assertEquals(
      procedure.edges.flatMap { listOf(it.source, it.target) }.toSet(),
      blocks.flatMap { it.locations }.toSet(),
    )
  }

  /** while (x < 10) { if (flag) x++ else x++ } - MERGE turns the body into a single self loop. */
  private fun branchingLoopProcedure(): XcfaProcedure =
    xcfa("branching-loop") {
        procedure("main") {
          "x" type Int()
          "flag" type Int()
          (init to "loophead") { "x" assign "0" }
          ("loophead" to "body") {
            assume("(< x 10)")
            havoc("flag")
          }
          ("loophead" to "afterloop") { assume("(>= x 10)") }
          ("body" to "bodyA") { assume("(= flag 0)") }
          ("body" to "bodyB") { assume("(/= flag 0)") }
          ("bodyA" to "bodyJoin") { "x" assign "(+ x 1)" }
          ("bodyB" to "bodyJoin") { "x" assign "(+ x 1)" }
          ("bodyJoin" to "loophead") { nop() }
          ("afterloop" to final) { assume("(= x 10)") }
          ("afterloop" to err) { assume("(/= x 10)") }
        }
      }
      .procedures
      .single()

  /** Nested loops: outer at "outer", inner at "inner"; nothing for plain MERGE to merge. */
  private fun nestedLoopProcedure(): XcfaProcedure =
    xcfa("nested-loop") {
        procedure("main") {
          "i" type Int()
          "j" type Int()
          (init to "outer") { "i" assign "0" }
          ("outer" to "inner") {
            assume("(< i 3)")
            "j" assign "0"
          }
          ("inner" to "innerBody") { assume("(< j 2)") }
          ("innerBody" to "inner") { "j" assign "(+ j 1)" }
          ("inner" to "afterInner") { assume("(>= j 2)") }
          ("afterInner" to "outer") { "i" assign "(+ i 1)" }
          ("outer" to "end") { assume("(>= i 3)") }
          ("end" to final) { nop() }
        }
      }
      .procedures
      .single()

  @Test
  fun `the self loop of MERGE is absorbed into the block entering the loop`() {
    val procedure = branchingLoopProcedure()
    val merged = MergeBlockDecomposition().decompose(procedure)
    assertEquals(1, merged.selfLoops().size, "sanity check: MERGE leaves a self loop")

    val absorbed = SelfLoopAbsorbingDecomposition().decompose(procedure)

    absorbed.checkConsistency()
    absorbed.assertCovers(procedure)
    assertTrue(absorbed.selfLoops().isEmpty())
    val loopBlock = absorbed.blocks.single { it.locations.any { loc -> loc.name == "bodyJoin" } }
    assertEquals(procedure.initLoc, loopBlock.initialLocation)
    assertTrue(
      absorbed.blocks.none {
        it.initialLocation.name == "loophead" || it.finalLocation.name == "loophead"
      }
    )
  }

  @Test
  fun `absorbing the inner loop turns the outer loop into a self loop that is absorbed too`() {
    val procedure = nestedLoopProcedure()
    val merged = MergeBlockDecomposition().decompose(procedure)
    assertEquals(1, merged.selfLoops().size, "sanity check: only the inner loop is a self loop")

    val absorbed = SelfLoopAbsorbingDecomposition().decompose(procedure)

    absorbed.checkConsistency()
    absorbed.assertCovers(procedure)
    assertTrue(absorbed.selfLoops().isEmpty())
    assertEquals(2, absorbed.blocks.size)
    assertEquals("outer", absorbed.root.finalLocation.name)
    assertTrue(absorbed.root.locations.map { it.name }.containsAll(listOf("inner", "afterInner")))
  }

  private fun twoEntriesGraph(secondExit: Boolean): BlockGraph {
    val (a, b, c, d) = listOf(loc("A"), loc("B"), loc("C"), loc("D"))
    val (e, f) = listOf(loc("E"), loc("F"))
    return BlockGraph.fromBlocksWithoutEdges(
      listOfNotNull(
        Block("r", a, b, setOf(a, b), emptySet()),
        Block("p", b, c, setOf(b, c), emptySet()),
        Block("q", b, d, setOf(b, d), emptySet()),
        Block("s", d, c, setOf(d, c), emptySet()),
        Block("l", c, c, setOf(c), emptySet()),
        Block("e1", c, e, setOf(c, e), emptySet()),
        if (secondExit) Block("e2", c, f, setOf(c, f), emptySet()) else null,
      )
    )
  }

  @Test
  fun `with several entering blocks the loop goes into the single leaving block`() {
    val absorbed = absorbSelfLoops(twoEntriesGraph(secondExit = false))

    absorbed.checkConsistency()
    assertTrue(absorbed.selfLoops().isEmpty())
    val host = absorbed.blocks.single { it.id == "ML0" }
    assertEquals("C", host.initialLocation.name)
    assertEquals("E", host.finalLocation.name)
    assertEquals(setOf("p", "s"), host.predecessorIds)
    assertEquals(setOf("r", "p", "q", "s", "ML0"), absorbed.blocks.map { it.id }.toSet())
  }

  @Test
  fun `a loop head with several entering and several leaving blocks is left alone`() {
    val graph = twoEntriesGraph(secondExit = true)
    assertSame(graph, absorbSelfLoops(graph))
  }
}
