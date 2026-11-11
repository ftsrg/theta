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

  private fun cutOf(
    graph: BlockGraph,
    id: String,
    decomposition: DssBlockDecomposition = DEFAULT_BLOCK_CUT,
  ): Pair<Block, BlockGraph> {
    val block = graph.blocks.single { it.id == id }
    val cut = checkNotNull(graph.cut(id, decomposition)) { "$id has no cut" }
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
  fun `a whole-loop block is cut by the linear decomposition at its branches and joins`() {
    val graph = MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).decompose(loopProcedure())
    val loopBlockId = graph.blocks.single { it.isRoot }.id
    val after = graph.blocks.single { !it.isRoot }
    val (_, cut) = cutOf(graph, loopBlockId, LinearBlockDecomposition())

    val wayIn = cut.root
    assertEquals("loophead", wayIn.finalLocation.name)
    val wayOut = cut.at("loophead", "afterloop")
    val intoLoop = cut.at("loophead", "body")
    val loopBack = cut.at("bodyJoin", "loophead")
    assertEquals(graph.blocks.size - 1 + 6, cut.blocks.size)
    assertEquals(setOf(wayOut.id, intoLoop.id), wayIn.successorIds)
    // The head is reached from the way in and from the loop, and left towards both
    assertEquals(setOf(wayIn.id, loopBack.id), wayOut.predecessorIds)
    assertEquals(setOf(wayIn.id, loopBack.id), intoLoop.predecessorIds)
    assertEquals(setOf(wayOut.id, intoLoop.id), loopBack.successorIds)
    // The way out is the only piece the next block hears from
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
    val (_, cut) = cutOf(graph, selfLoop.id, LinearBlockDecomposition())

    val body = cut.at("h", "h")
    val exits = cut.blocks.filter { it.initialLocation.name == "h" && it != body }
    assertEquals(2, body.edges.size)
    assertEquals(3, exits.size)
    // The body comes back to the head, so it is left by the body and by every exit
    assertEquals(exits.map { it.id }.toSet() + body.id, body.successorIds)
    assertEquals(exits.map { it.id }.toSet() + body.id, cut.root.successorIds)
    assertTrue(body.id in body.predecessorIds)
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
    val (_, cut) = cutOf(graph, "rest", LinearBlockDecomposition())
    assertEquals(3, cut.blocks.size)
    assertEquals(setOf("rest_0", "rest_1"), cut.root.successorIds)
    assertTrue(cut.blocks.filter { it != cut.root }.all { it.initialLocation == s })

    val single = SingleBlockDecomposition.decompose(procedure)
    val (_, rootCut) = cutOf(single, single.root.id, LinearBlockDecomposition())
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
    val (_, cut) = cutOf(graph, loopBlock.id, LinearBlockDecomposition())

    val toStep = cut.at("h", "step")
    val backToHead = cut.blocks.filter { it.initialLocation.name == "step" }
    val skip = backToHead.single { it.edges.size == 1 }
    val increment = backToHead.single { it.edges.size == 2 }
    // Whatever comes back to the head is a predecessor of the pieces that start there
    assertEquals(setOf(cut.root.id, skip.id, increment.id), toStep.predecessorIds)
    assertTrue(skip.id in toStep.predecessorIds && increment.id in toStep.predecessorIds)
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

  /** init -> a, a -> c over b1 or b2, then c -> d -> e -> final: eight edges, a diamond inside. */
  private fun diamondChainProcedure(): XcfaProcedure =
    xcfa("diamondChain") {
        procedure("main") {
          "x" type Int()
          (init to "a") { "x" assign "0" }
          ("a" to "b1") { assume("(< x 1)") }
          ("a" to "b2") { assume("(>= x 1)") }
          ("b1" to "c") { "x" assign "1" }
          ("b2" to "c") { "x" assign "2" }
          ("c" to "d") { "x" assign "3" }
          ("d" to "e") { "x" assign "4" }
          ("e" to final) { "x" assign "5" }
        }
      }
      .procedures
      .single()

  private val decompositions: Map<String, DssBlockDecomposition> =
    linkedMapOf(
      "LINEAR" to LinearBlockDecomposition(),
      "MERGE" to MergeBlockDecomposition(),
      "MERGE_ABSORB_SELF_LOOPS" to SelfLoopAbsorbingDecomposition(),
      "MERGE_ACYCLIC" to AcyclicMergeDecomposition(),
      "MIN_CUT" to MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW),
      "MIN_CUT_ABSORB_SELF_LOOPS" to
        MinCutDecomposition(loopHandling = CutLoopHandling.ABSORB_SELF_LOOPS),
      "MIN_CUT_ACYCLIC" to MinCutDecomposition(loopHandling = CutLoopHandling.FORBID),
      "NONE" to SingleBlockDecomposition,
    )

  private val diamondBlock: Block by lazy {
    SingleBlockDecomposition.decompose(diamondChainProcedure()).root
  }

  @Test
  fun `the linear decomposition cuts a block at every branch and join`() {
    val pieces = checkNotNull(cutBlock(diamondBlock, LinearBlockDecomposition()))
    assertCovers(diamondBlock, pieces)
    // init -> a, the two ways from a to c, and c to the end
    assertEquals(listOf(1, 2, 2, 3), pieces.map { it.edges.size }.sorted())
  }

  @Test
  fun `the merge decomposition cuts a block in two`() {
    val pieces = checkNotNull(cutBlock(diamondBlock, MergeBlockDecomposition()))
    assertCovers(diamondBlock, pieces)
    assertEquals(2, pieces.size)
  }

  @Test
  fun `the min-cut decomposition cuts a block where fewest edges go between the pieces`() {
    val pieces = checkNotNull(cutBlock(diamondBlock, MinCutDecomposition()))
    assertCovers(diamondBlock, pieces)
    assertEquals(2, pieces.size)
    assertEquals(
      pieces.single { it.initialLocation == diamondBlock.initialLocation }.finalLocation,
      pieces.single { it.finalLocation == diamondBlock.finalLocation }.initialLocation,
    )
  }

  @Test
  fun `the default cut is the min-cut decomposition that absorbs self loops`() {
    assertEquals(
      cutBlock(diamondBlock, MinCutDecomposition(loopHandling = CutLoopHandling.ABSORB_SELF_LOOPS)),
      cutBlock(diamondBlock),
    )
  }

  @Test
  fun `no decomposition means no cut`() {
    assertNull(cutBlock(diamondBlock, SingleBlockDecomposition))
  }

  @Test
  fun `a decomposition that cannot handle the block gives no cut`() {
    assertNull(cutBlock(diamondBlock, DssBlockDecomposition { error("unsupported") }))
  }

  @Test
  fun `a decomposition whose pieces lose a path gives no cut`() {
    val lossy = DssBlockDecomposition { procedure ->
      val whole = SingleBlockDecomposition.decompose(procedure).root
      val kept = whole.edges.take(whole.edges.size - 1).toSet()
      val last = kept.last()
      BlockGraph.fromBlocksWithoutEdges(
        listOf(
          whole.copy(id = "a", edges = kept, finalLocation = last.target),
          whole.copy(id = "b", edges = setOf(last), initialLocation = last.target),
        )
      )
    }
    assertNull(cutBlock(diamondBlock, lossy))
  }

  @Test
  fun `every decomposition cuts a block into pieces that keep its paths, or does not cut it`() {
    val blocks =
      listOf(chainProcedure(), branchProcedure(), diamondChainProcedure()).map {
        SingleBlockDecomposition.decompose(it).root
      } +
        MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).decompose(loopProcedure()).blocks
    for ((name, decomposition) in decompositions) {
      for (block in blocks) {
        val pieces = cutBlock(block, decomposition) ?: continue
        assertTrue(pieces.size >= 2) { "$name gave ${pieces.size} pieces for ${block.id}" }
        assertCovers(block, pieces)
      }
    }
  }

  @Test
  fun `every decomposition replaces a block of a graph by pieces that keep it consistent`() {
    val graph = MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).decompose(loopProcedure())
    for ((name, decomposition) in decompositions) {
      for (block in graph.blocks) {
        val cut = graph.cut(block.id, decomposition) ?: continue
        cut.checkConsistency()
        assertTrue(cut.blocks.size > graph.blocks.size) { "$name did not split ${block.id}" }
      }
    }
  }

  @Test
  fun `the pieces of a block take over its neighbors`() {
    val graph = MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW).decompose(loopProcedure())
    val after = graph.blocks.single { !it.isRoot }
    val cut = checkNotNull(graph.cut(after.id, LinearBlockDecomposition()))
    val pieces = cut.blocks.filter { it.id.startsWith("${after.id}_") }
    val entries = pieces.filter { it.initialLocation == after.initialLocation }
    assertTrue(entries.isNotEmpty())
    assertTrue(entries.all { graph.root.id in it.predecessorIds })
    assertEquals(entries.map { it.id }.toSet(), cut.root.successorIds)
  }
}
