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
package hu.bme.mit.theta.xcfa.analysis.dss.decomposition

import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class MinCutDecompositionTest {

  private fun MinCut.assertCovers(procedure: XcfaProcedure) {
    blockGraph.checkConsistency()
    assertEquals(procedure.edges, blockGraph.blocks.flatMap { it.edges }.toSet())
    val edges = blockGraph.blocks.flatMap { it.edges }
    assertEquals(edges.size, edges.toSet().size, "an edge is in two blocks")
  }

  private fun MinCut.sizes() = cutBlocks.map { it.locations.size }

  /** while (x < 10) { if (flag) x++ else x++ } then a check after the loop. */
  private fun loopProcedure(): XcfaProcedure =
    xcfa("loop") {
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

  /** init -> a -> b -> c -> d -> final */
  private fun chainProcedure(): XcfaProcedure =
    xcfa("chain") {
        procedure("main") {
          "x" type Int()
          (init to "a") { "x" assign "0" }
          ("a" to "b") { "x" assign "1" }
          ("b" to "c") { "x" assign "2" }
          ("c" to "d") { "x" assign "3" }
          ("d" to final) { "x" assign "4" }
        }
      }
      .procedures
      .single()

  private fun threeExitLoopProcedure(): XcfaProcedure =
    xcfa("three-exit-loop") {
        procedure("main") {
          "x" type Int()
          (init to "h") { "x" assign "0" }
          ("h" to "b") { assume("(< x 10)") }
          ("b" to "h") { "x" assign "(+ x 1)" }
          ("h" to "x1") { assume("(= x 10)") }
          ("h" to "x2") { assume("(= x 11)") }
          ("h" to "x3") { assume("(> x 11)") }
          ("x1" to "j") { nop() }
          ("x2" to "j") { nop() }
          ("x3" to "j") { nop() }
          ("j" to final) { nop() }
        }
      }
      .procedures
      .single()

  /** init -> h, h -> b -> h: a loop without exit; its only cut, at `h`, is a self loop. */
  private fun endlessLoopProcedure(): XcfaProcedure =
    xcfa("endless") {
        procedure("main") {
          "x" type Int()
          (init to "h") { "x" assign "0" }
          ("h" to "b") { nop() }
          ("b" to "h") { "x" assign "(+ x 1)" }
        }
      }
      .procedures
      .single()

  @Test
  fun `the loop is cut at its single exit edge, in all three versions`() {
    val procedure = loopProcedure()
    for (handling in CutLoopHandling.entries) {
      val cut = MinCutDecomposition(loopHandling = handling).cut(procedure)

      cut.assertCovers(procedure)
      assertEquals(listOf("afterloop"), cut.cutLocations.map { it.name }, "$handling")
      assertEquals(1, cut.cutEdges.size)
      assertEquals(2, cut.blockGraph.blocks.size)
      assertTrue(cut.exhaustive)
    }
  }

  @Test
  fun `among equally cheap cuts the most balanced one is chosen`() {
    val procedure = chainProcedure()

    val two = MinCutDecomposition(blockCount = 2).cut(procedure)
    two.assertCovers(procedure)
    assertEquals(1, two.cutEdges.size)
    assertTrue(two.sizes().max() - two.sizes().min() <= 1, "${two.sizes()}")

    val three = MinCutDecomposition(blockCount = 3).cut(procedure)
    three.assertCovers(procedure)
    assertEquals(3, three.blockGraph.blocks.size)
    assertEquals(2, three.cutEdges.size)
    assertTrue(three.sizes().max() - three.sizes().min() <= 1, "${three.sizes()}")
  }

  @Test
  fun `more blocks than the procedure can be cut into gives as many as possible`() {
    val procedure = chainProcedure()

    val cut = MinCutDecomposition(blockCount = 10).cut(procedure)

    cut.assertCovers(procedure)
    assertEquals(10, cut.requestedBlockCount)
    assertEquals(5, cut.blockGraph.blocks.size)
  }

  @Test
  fun `the three versions differ where the cheapest cut makes a self loop`() {
    val procedure = threeExitLoopProcedure()

    val allow = MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).cut(procedure)
    allow.assertCovers(procedure)
    assertEquals(listOf("h"), allow.cutLocations.map { it.name })
    assertEquals(1, allow.blockGraph.getStatistics().selfLoops)

    val absorb =
      MinCutDecomposition(loopHandling = CutLoopHandling.ABSORB_SELF_LOOPS).cut(procedure)
    absorb.assertCovers(procedure)
    assertEquals(listOf("h"), absorb.cutLocations.map { it.name })
    assertEquals(0, absorb.blockGraph.getStatistics().cyclicSccs)

    val acyclic = MinCutDecomposition(loopHandling = CutLoopHandling.FORBID).cut(procedure)
    acyclic.assertCovers(procedure)
    assertEquals(listOf("j"), acyclic.cutLocations.map { it.name })
    assertEquals(3, acyclic.cutEdges.size)
    assertEquals(0, acyclic.blockGraph.getStatistics().cyclicSccs)
    assertEquals(2, acyclic.blockGraph.blocks.size)
  }

  @Test
  fun `an impossible acyclic cut falls back to the plain min cut`() {
    val procedure = endlessLoopProcedure()

    val plain = MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).cut(procedure)
    val acyclic = MinCutDecomposition(loopHandling = CutLoopHandling.FORBID).cut(procedure)

    assertEquals(listOf("h"), plain.cutLocations.map { it.name })
    assertEquals(null, plain.fallbackReason)
    assertEquals(plain.cutLocations, acyclic.cutLocations)
    assertEquals(1, acyclic.blockGraph.getStatistics().selfLoops)
    assertTrue(acyclic.fallbackReason!!.contains("acyclic"), acyclic.fallbackReason)
    assertTrue(acyclic.describe()[0].contains("fell back to MIN_CUT"), acyclic.describe()[0])
  }

  @Test
  fun `the fallback is a single block where the plain min cut is one`() {
    val procedure =
      xcfa("straight") {
          procedure("main") {
            "x" type Int()
            (init to final) { "x" assign "0" }
          }
        }
        .procedures
        .single()

    for (handling in CutLoopHandling.entries) {
      for (blocks in listOf(1, 2)) {
        val cut = MinCutDecomposition(blocks, handling).cut(procedure)
        assertEquals(1, cut.blockGraph.blocks.size, "$handling, $blocks")
        assertEquals(handling != CutLoopHandling.ALLOW, cut.fallbackReason != null, "$handling")
      }
    }
  }

  @Test
  fun `the report lists the cut edges and the blocks before and after the cut`() {
    val lines = MinCutDecomposition().cut(loopProcedure()).describe()

    assertTrue(lines[0].startsWith("DSS min cut: 2 blocks (requested 2), 1 cut edges"), lines[0])
    assertTrue(lines.any { it.startsWith("DSS min cut edge: loophead -> afterloop") }, "$lines")
    assertTrue(
      lines.any { it.contains("(before the cut)") && it.contains("-> afterloop") },
      "$lines",
    )
    assertTrue(
      lines.any { it.contains("(after the cut)") && it.contains("afterloop ->") },
      "$lines",
    )
  }

  @Test
  fun `a search stopped at its budget still returns a valid cut`() {
    val procedure = chainProcedure()

    val cut = MinCutDecomposition(searchBudget = 1).cut(procedure)

    cut.assertCovers(procedure)
    assertFalse(cut.exhaustive)
    assertEquals(2, cut.blockGraph.blocks.size)
  }
}
