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
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

/** The message passing of both in-process executors, with stub block analyses. */
class DssExecutorTest {

  enum class Executor(val run: (BlockGraph, (Block) -> DssBlockBehavior) -> DssResult) {
    CONCURRENT({ graph, behaviorFor -> runDssActors(graph, behaviorFor) }),
    SEQUENTIAL({ graph, behaviorFor -> runDssActorsSequentially(graph, behaviorFor) }),
  }

  private fun block(
    id: String,
    predecessorIds: Set<String> = emptySet(),
    successorIds: Set<String> = emptySet(),
  ): Block {
    val entry = XcfaLocation("$id-in", metadata = EmptyMetaData)
    val exit = XcfaLocation("$id-out", metadata = EmptyMetaData)
    return Block(id, entry, exit, setOf(entry, exit), emptySet(), predecessorIds, successorIds)
  }

  private fun Executor.runEcho(blockGraph: BlockGraph, violatingBlock: String? = null) =
    assertTimeoutPreemptively<DssResult>(Duration.ofSeconds(10)) {
      run(blockGraph) { EchoBlockAnalysis(it.id, originatesViolation = it.id == violatingBlock) }
    }

  private fun chain() =
    BlockGraph(
      setOf(
        block("R", successorIds = setOf("A")),
        block("A", predecessorIds = setOf("R"), successorIds = setOf("B")),
        block("B", predecessorIds = setOf("A")),
      )
    )

  private fun join() =
    BlockGraph(
      setOf(
        block("R", successorIds = setOf("A", "B")),
        block("A", predecessorIds = setOf("R"), successorIds = setOf("C")),
        block("B", predecessorIds = setOf("R"), successorIds = setOf("C")),
        block("C", predecessorIds = setOf("A", "B")),
      )
    )

  private fun selfLoop() =
    BlockGraph(
      setOf(
        block("R", successorIds = setOf("LH")),
        block("LH", predecessorIds = setOf("R", "LH"), successorIds = setOf("LH", "X")),
        block("X", predecessorIds = setOf("LH")),
      )
    )

  @ParameterizedTest
  @EnumSource(Executor::class)
  fun `without violations the run ends SAFE`(executor: Executor) {
    assertEquals(DssResult.SAFE, executor.runEcho(chain()))
    assertEquals(DssResult.SAFE, executor.runEcho(join()))
    assertEquals(DssResult.SAFE, executor.runEcho(selfLoop()))
  }

  @ParameterizedTest
  @EnumSource(Executor::class)
  fun `a violation propagates back to the root and ends UNSAFE`(executor: Executor) {
    assertEquals(DssResult.UNSAFE, executor.runEcho(chain(), violatingBlock = "B"))
    assertEquals(DssResult.UNSAFE, executor.runEcho(join(), violatingBlock = "C"))
    assertEquals(DssResult.UNSAFE, executor.runEcho(selfLoop(), violatingBlock = "X"))
  }
}
