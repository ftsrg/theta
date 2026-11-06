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
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class BlockCutTest {

  /** The pieces share no edge, cover the block, and take every edge out of what they pass. */
  private fun assertCovers(block: Block, pieces: List<Block>) {
    assertEquals(block.edges, pieces.flatMap { it.edges }.toSet())
    assertEquals(block.edges.size, pieces.sumOf { it.edges.size }, "an edge is in two pieces")
    for (piece in pieces) {
      for (location in piece.locations - piece.initialLocation - piece.finalLocation) {
        val leaving = location.outgoingEdges.filter { it in block.edges }
        assertTrue(piece.edges.containsAll(leaving)) { "${piece.id} leaves ${location.name}" }
      }
    }
  }

  private fun cutOf(graph: BlockGraph, id: String): Pair<Block, BlockGraph> {
    val block = graph.blocks.single { it.id == id }
    val cut = checkNotNull(graph.cut(id)) { "$id has no cut" }
    assertCovers(block, cut.blocks.filter { it.id.startsWith("${id}_") })
    return block to cut
  }

  private fun BlockGraph.at(initial: String, final: String) =
    blocks.single { it.initialLocation.name == initial && it.finalLocation.name == final }

  private fun XcfaProcedure.location(name: String) = locs.single { it.name == name }

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

  /** init -> s, then two branches from s to the end. */
  private fun branchProcedure(): XcfaProcedure =
    xcfa("branch") {
        procedure("main") {
          "x" type Int()
          (init to "s") { "x" assign "0" }
          ("s" to "l") { assume("(< x 1)") }
          ("s" to "r") { assume("(>= x 1)") }
          ("l" to final) { "x" assign "1" }
          ("r" to final) { "x" assign "2" }
        }
      }
      .procedures
      .single()

  @Test
  fun `a chain is cut in two at its middle`() {
    val (block, cut) = cutOf(SingleBlockDecomposition.decompose(chainProcedure()), "SB1")
    assertEquals(2, cut.blocks.size)
    val first = cut.root
    assertEquals(block.initialLocation, first.initialLocation)
    assertEquals("b", first.finalLocation.name)
    assertEquals(listOf(2, 3), cut.blocks.map { it.edges.size }.sorted())
    assertEquals(first.successorIds, cut.blocks.filter { it != first }.map { it.id }.toSet())
  }

  @Test
  fun `a whole-loop block is cut at its head into the way in, the loop and the way out`() {
    val graph = MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).decompose(loopProcedure())
    val loopBlockId = graph.blocks.single { it.isRoot }.id
    val after = graph.blocks.single { !it.isRoot }
    val (_, cut) = cutOf(graph, loopBlockId)

    val wayIn = cut.root
    assertEquals("loophead", wayIn.finalLocation.name)
    val loop = cut.at("loophead", "loophead")
    val wayOut = cut.at("loophead", "afterloop")
    assertEquals(4, cut.blocks.size)
    assertEquals(wayIn, cut.root)
    assertEquals(setOf(loop.id, wayOut.id), wayIn.successorIds)
    assertEquals(setOf(loop.id, wayOut.id), loop.successorIds)
    assertEquals(setOf(after.id), wayOut.successorIds)
    assertEquals(setOf(wayOut.id), cut.blocks.single { it.id == after.id }.predecessorIds)
  }

  @Test
  fun `a self loop splits into its body and its exit without a cut location`() {
    val procedure =
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
    val graph = MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).decompose(procedure)
    val selfLoop = graph.blocks.single { it.id in it.successorIds }
    val (_, cut) = cutOf(graph, selfLoop.id)

    val body = cut.at("h", "h")
    val exit = cut.blocks.single { it.initialLocation.name == "h" && it != body }
    assertEquals(3, cut.blocks.size)
    assertEquals(2, body.edges.size)
    assertEquals(setOf(body.id, exit.id), body.successorIds)
    assertEquals(setOf(body.id, exit.id), cut.root.successorIds)
    assertTrue(exit.successorIds.isEmpty())
  }

  @Test
  fun `the branches of a block's entry become parallel pieces, but not those of the root`() {
    val procedure = branchProcedure()
    val s = procedure.location("s")
    val enter = procedure.edges.single { it.target == s }
    val rest = procedure.edges - enter
    val graph =
      BlockGraph.fromBlocksWithoutEdges(
        listOf(
          Block("in", procedure.initLoc, s, setOf(procedure.initLoc, s), setOf(enter)),
          Block(
            "rest",
            s,
            procedure.finalLoc.get(),
            rest.flatMap { listOf(it.source, it.target) }.toSet(),
            rest,
          ),
        )
      )
    val (_, cut) = cutOf(graph, "rest")
    assertEquals(3, cut.blocks.size)
    assertEquals(setOf("rest_0", "rest_1"), cut.root.successorIds)
    assertTrue(cut.blocks.filter { it != cut.root }.all { it.initialLocation == s })

    val single = SingleBlockDecomposition.decompose(procedure)
    val (_, rootCut) = cutOf(single, single.root.id)
    assertEquals(1, rootCut.blocks.count { it.initialLocation == procedure.initLoc })
  }

  @Test
  fun `a loop block entered at its head is cut where the loop comes back to it`() {
    val procedure =
      xcfa("counter") {
          procedure("main") {
            "x" type Int()
            (init to "h") { "x" assign "1" }
            ("h" to err) { assume("(= x 5)") }
            ("h" to "step") { assume("(/= x 5)") }
            ("step" to "h") { nop() }
            ("step" to "inc") { assume("(< x 4)") }
            ("inc" to "h") { "x" assign "(+ x 1)" }
          }
        }
        .procedures
        .single()
    val graph =
      MinCutDecomposition(loopHandling = CutLoopHandling.ABSORB_SELF_LOOPS).decompose(procedure)
    val loopBlock = graph.blocks.single { !it.isRoot }
    assertTrue(loopBlock.initialLocation.name == "h" && loopBlock.finalLocation.error) {
      "fixture shape: ${loopBlock.initialLocation} -> ${loopBlock.finalLocation}"
    }
    val (_, cut) = cutOf(graph, loopBlock.id)

    val loop = cut.at("h", "h")
    val exit = cut.blocks.single { it.initialLocation.name == "h" && it != loop }
    assertEquals(setOf(cut.root.id, loop.id), loop.predecessorIds)
    assertEquals(setOf(cut.root.id, loop.id), exit.predecessorIds)
  }

  @Test
  fun `a single edge has no cut`() {
    val procedure =
      xcfa("straight") {
          procedure("main") {
            "x" type Int()
            (init to final) { "x" assign "0" }
          }
        }
        .procedures
        .single()
    val graph = SingleBlockDecomposition.decompose(procedure)
    assertNull(cutBlock(graph.root))
    assertNull(graph.cut(graph.root.id))
  }
}
