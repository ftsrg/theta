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
import java.util.concurrent.LinkedBlockingQueue
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** The ASCII escape byte (0x1B) that ANSI color codes start with. */
private const val ANSI_ESCAPE_BYTE = ""

/**
 * Build-order step 7: given a `visualizationLog`, both executors record the run's message traffic
 * without changing the verdict.
 */
class DssVisualizationActorTest {

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

  private fun straightChain(): BlockGraph {
    val root = block("R", successorIds = setOf("A"))
    val a = block("A", predecessorIds = setOf("R"), successorIds = setOf("B"))
    val b = block("B", predecessorIds = setOf("A"))
    return BlockGraph(setOf(root, a, b))
  }

  @Test
  fun `the concurrent executor's visualization log captures the full run without changing the verdict`() {
    val blockGraph = straightChain()
    val log = mutableListOf<DssLogEntry>()

    val result =
      assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(10)) {
        runDssActors(blockGraph, { EchoBlockAnalysis(it.id) }, visualizationLog = log)
      }

    assertEquals(DssResult.SAFE, result)
    assertLogCapturesFullRun(log, blockGraph)
  }

  @Test
  fun `the sequential executor's visualization log captures the full run without changing the verdict`() {
    val blockGraph = straightChain()
    val log = mutableListOf<DssLogEntry>()

    val result =
      assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(10)) {
        runDssActorsSequentially(blockGraph, { EchoBlockAnalysis(it.id) }, visualizationLog = log)
      }

    assertEquals(DssResult.SAFE, result)
    assertLogCapturesFullRun(log, blockGraph)
  }

  @Test
  fun `an UNSAFE run is captured too, including the violation condition`() {
    // The violation must originate in a *non-root* block: a root that finds one locally shortcuts
    // straight to broadcasting RESULT(UNSAFE) without ever putting a VIOLATION_CONDITION message
    // on the wire at all (see DssBlockActor.broadcast) - a leaf's violation, by contrast, has to be
    // routed back to the root first, which is the message this test wants to see captured.
    val root = block("R", successorIds = setOf("A"))
    val leaf = block("A", predecessorIds = setOf("R"))
    val blockGraph = BlockGraph(setOf(root, leaf))
    val log = mutableListOf<DssLogEntry>()

    val result =
      assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(10)) {
        runDssActors(
          blockGraph,
          { block -> EchoBlockAnalysis(block.id, originatesViolation = block.id == "A") },
          visualizationLog = log,
        )
      }

    assertEquals(DssResult.UNSAFE, result)
    assertTrue(log.any { it.message.type == DssMessageType.VIOLATION_CONDITION })
    assertTrue(
      log.any {
        it.message is DssResultMessage &&
          (it.message as DssResultMessage).result == DssResult.UNSAFE
      }
    )
  }

  @Test
  fun `rendering produces one line per entry, and only the colored variant carries ANSI escapes`() {
    val blockGraph = straightChain()
    val log = mutableListOf<DssLogEntry>()
    runDssActorsSequentially(blockGraph, { EchoBlockAnalysis(it.id) }, visualizationLog = log)

    val connection =
      DssConnection(LinkedBlockingQueue(), DssMessageBroadcaster(emptyMap()), mutableSetOf())
    val visualizer = DssVisualizationActor("v", connection, blockGraph.blocks.size, log)

    val plain = visualizer.renderTextLog()
    val colored = visualizer.renderAnsiColoredLog()

    assertEquals(log.size, plain.lines().size)
    assertEquals(log.size, colored.lines().size)
    assertFalse(plain.contains(ANSI_ESCAPE_BYTE), "plain rendering must not contain ANSI escapes")
    assertTrue(colored.contains(ANSI_ESCAPE_BYTE), "colored rendering must contain ANSI escapes")
  }

  private fun assertLogCapturesFullRun(log: List<DssLogEntry>, blockGraph: BlockGraph) {
    assertTrue(log.isNotEmpty(), "expected the visualization log to capture something")
    assertTrue(
      log.zipWithNext().all { (a, b) -> a.timestampMillis <= b.timestampMillis },
      "log entries should be in non-decreasing timestamp order",
    )
    assertTrue(log.any { it.message.type == DssMessageType.RESULT })
    for (block in blockGraph.blocks) {
      assertTrue(
        log.any { it.message.type == DssMessageType.STATISTIC && it.message.senderId == block.id },
        "expected a STATISTIC from ${block.id} in the log",
      )
    }
  }
}
