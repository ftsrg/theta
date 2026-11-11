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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssBlockCutRequest
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.time.Duration
import java.util.concurrent.CopyOnWriteArrayList
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/**
 * `runDssNetworksSequentially` with a cutter: the block that asks to be cut is replaced by its
 * pieces, which hear what its neighbors last said to it, and no other block starts over.
 */
class DssInPlaceCutTest {

  private fun location(name: String) = XcfaLocation(name, metadata = EmptyMetaData)

  private val entry = location("A-in")
  private val middle = location("A-mid")
  private val exit = location("A-out")

  private fun block(
    id: String,
    predecessorIds: Set<String> = emptySet(),
    successorIds: Set<String> = emptySet(),
    initial: XcfaLocation = location("$id-in"),
    final: XcfaLocation = location("$id-out"),
  ) = Block(id, initial, final, setOf(initial, final), emptySet(), predecessorIds, successorIds)

  /** R -> A -> B, with the blocks in the order in which they start. */
  private fun chain(order: List<String>): BlockGraph {
    val blocks =
      mapOf(
        "R" to block("R", successorIds = setOf("A")),
        "A" to block("A", setOf("R"), setOf("B"), initial = entry, final = exit),
        "B" to block("B", predecessorIds = setOf("A")),
      )
    return BlockGraph(order.map { blocks.getValue(it) }.toCollection(linkedSetOf()))
  }

  /** `A` as `A_0` (entry to middle) and `A_1` (middle to exit), the neighbors rewired. */
  private val cutter = DssBlockCutter { graph, id ->
    if (id != "A") return@DssBlockCutter null
    val blocks = graph.blocks.associateBy { it.id }
    val a = blocks.getValue("A")
    val first =
      Block("A_0", entry, middle, setOf(entry, middle), emptySet(), setOf("R"), setOf("A_1"))
    val second =
      Block("A_1", middle, exit, setOf(middle, exit), emptySet(), setOf("A_0"), setOf("B"))
    BlockGraph(
      linkedSetOf(
        blocks.getValue("R").copy(successorIds = setOf("A_0")),
        first,
        second,
        blocks.getValue("B").copy(predecessorIds = setOf("A_1")),
      )
    )
  }

  /** Echoes like [EchoBlockAnalysis] and logs what happens to the block. */
  private class Recording(
    private val id: String,
    private val log: MutableList<String>,
    private val cutAt: String? = null,
    private val violates: Boolean = false,
  ) : DssBlockBehavior {

    private val echo = EchoBlockAnalysis(id, originatesViolation = violates)

    private fun cutIf(event: String) {
      if (cutAt == event) throw DssBlockCutRequest(id)
    }

    override fun initialMessages(): Collection<DssMessage> {
      log += "$id:start"
      cutIf("start")
      return echo.initialMessages()
    }

    override fun onPostCondition(message: DssPostConditionMessage): Collection<DssMessage> {
      log += "$id:post<-${message.senderId}"
      cutIf("post")
      return echo.onPostCondition(message)
    }

    override fun onViolationCondition(
      message: DssViolationConditionMessage
    ): Collection<DssMessage> {
      log += "$id:vc<-${message.senderId}"
      return echo.onViolationCondition(message)
    }

    override fun onNeighborReplaced(oldId: String, block: Block, replacements: Set<String>) {
      log +=
        "$id:replaced($oldId by ${replacements.sorted()}):" +
          "preds=${block.predecessorIds.sorted()},succs=${block.successorIds.sorted()}"
    }
  }

  private fun run(
    graph: BlockGraph,
    log: MutableList<String>,
    cutAt: String,
    violatingBlock: String? = null,
  ): DssRun =
    assertTimeoutPreemptively<DssRun>(Duration.ofSeconds(10)) {
      runDssNetworksSequentially(
        listOf(
          DssNetwork(graph) {
            Recording(
              it.id,
              log,
              cutAt = cutAt.takeIf { _ -> it.id == "A" },
              violates = it.id == violatingBlock,
            )
          }
        ),
        cutter = cutter,
      )
    }

  @Test
  fun `a block cut when a message arrives is replaced by pieces that hear the latest post`() {
    val log = CopyOnWriteArrayList<String>()
    val run = run(chain(listOf("R", "A", "B")), log, cutAt = "post")

    assertEquals(DssResult.SAFE, run.result)
    assertEquals(
      setOf("R", "A_0", "A_1", "B"),
      run.blockGraphs.single().blocks.map { it.id }.toSet(),
    )
    // The pieces start, and the entry piece is told what the predecessor last sent
    assertTrue("A_0:start" in log && "A_1:start" in log) { "$log" }
    assertTrue("A_0:post<-R" in log) { "$log" }
    assertTrue("A_1:post<-A_0" in log && "B:post<-A_1" in log) { "$log" }
    // The neighbors forget the block and adopt the pieces
    assertTrue("R:replaced(A by [A_0]):preds=[],succs=[A_0]" in log) { "$log" }
    assertTrue("B:replaced(A by [A_1]):preds=[A_1],succs=[]" in log) { "$log" }
    // What the block had sent before it was cut is not delivered
    assertFalse("B:post<-A" in log) { "$log" }
  }

  @Test
  fun `no other block starts over`() {
    val log = CopyOnWriteArrayList<String>()
    run(chain(listOf("R", "A", "B")), log, cutAt = "post")
    assertEquals(1, log.count { it == "R:start" })
    assertEquals(1, log.count { it == "B:start" })
    assertEquals(1, log.count { it == "A:start" })
  }

  @Test
  fun `the exit piece hears the latest violation condition of the successor`() {
    val log = CopyOnWriteArrayList<String>()
    // B starts first, so its violation condition is queued at A when A is cut at its start
    val run = run(chain(listOf("B", "R", "A")), log, cutAt = "start", violatingBlock = "B")

    assertEquals(DssResult.UNSAFE, run.result)
    // The root that reports it may be a piece, which is still in the one network
    assertEquals(0, run.network)
    assertTrue("A_1:vc<-B" in log) { "$log" }
    assertTrue("A_0:vc<-A_1" in log && "R:vc<-A_0" in log) { "$log" }
    assertFalse("R:vc<-A" in log) { "$log" }
  }

  @Test
  fun `a block that starts after the cut hears from the pieces`() {
    val log = CopyOnWriteArrayList<String>()
    val run = run(chain(listOf("R", "A", "B")), log, cutAt = "start")

    assertEquals(DssResult.SAFE, run.result)
    assertTrue("B:post<-A_1" in log) { "$log" }
    assertFalse("B:post<-A" in log) { "$log" }
    assertNotNull(run.blockGraphs.singleOrNull())
  }

  @Test
  fun `a block without a cut fails the network as before`() {
    val log = CopyOnWriteArrayList<String>()
    val noCut = DssBlockCutter { _, _ -> null }
    assertThrows<IllegalStateException> {
      assertTimeoutPreemptively<DssRun>(Duration.ofSeconds(10)) {
        runDssNetworksSequentially(
          listOf(
            DssNetwork(chain(listOf("R", "A", "B"))) {
              Recording(it.id, log, cutAt = "post".takeIf { _ -> it.id == "A" })
            }
          ),
          cutter = noCut,
        )
      }
    }
  }

  @Test
  fun `without a cutter the request fails the network`() {
    val log = CopyOnWriteArrayList<String>()
    assertThrows<IllegalStateException> {
      assertTimeoutPreemptively<DssRun>(Duration.ofSeconds(10)) {
        runDssNetworksSequentially(
          listOf(
            DssNetwork(chain(listOf("R", "A", "B"))) {
              Recording(it.id, log, cutAt = "post".takeIf { _ -> it.id == "A" })
            }
          )
        )
      }
    }
  }
}
