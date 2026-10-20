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
import java.util.concurrent.LinkedBlockingQueue

private const val SEQUENTIAL_OBSERVER_ID = "__observer__"
private const val SEQUENTIAL_VISUALIZER_ID = "__visualizer__"
private const val SEQUENTIAL_EXECUTOR_ID = "sequential-executor"

/** CPAchecker's `SequentialDssExecutor`: round-robin, SAFE once every queue is empty. */
fun runDssActorsSequentially(
  blockGraph: BlockGraph,
  behaviorFor: (Block) -> DssBlockBehavior,
  visualizationLog: MutableList<DssLogEntry>? = null,
): DssResult {
  val active = mutableSetOf<String>()
  val extraIds = if (visualizationLog != null) setOf(SEQUENTIAL_VISUALIZER_ID) else emptySet()
  val inboxes =
    (blockGraph.blocks.map { it.id }.sorted() + SEQUENTIAL_OBSERVER_ID + extraIds).associateWith {
      // Arrival order, so the final messages can't end the visualizer's run early
      if (it == SEQUENTIAL_VISUALIZER_ID) LinkedBlockingQueue<DssMessage>()
      else createDssMessageQueue()
    }
  val connectionsForBroadcaster =
    inboxes.mapValues { (id, queue) ->
      val role =
        if (id == SEQUENTIAL_OBSERVER_ID || id == SEQUENTIAL_VISUALIZER_ID) DssActorRole.OBSERVER
        else DssActorRole.BLOCK
      role to queue
    }
  val broadcaster = DssMessageBroadcaster(connectionsForBroadcaster)

  val observer =
    DssObserverActor(
      SEQUENTIAL_OBSERVER_ID,
      DssConnection(inboxes.getValue(SEQUENTIAL_OBSERVER_ID), broadcaster, active),
      blockGraph.blocks.size,
    )
  val blockActors =
    blockGraph.blocks.associate { block ->
      block.id to
        DssBlockActor(
          block,
          DssConnection(inboxes.getValue(block.id), broadcaster, active),
          behaviorFor(block),
        )
    }
  val visualizer =
    visualizationLog?.let {
      DssVisualizationActor(
        SEQUENTIAL_VISUALIZER_ID,
        DssConnection(inboxes.getValue(SEQUENTIAL_VISUALIZER_ID), broadcaster, active),
        blockGraph.blocks.size,
        it,
      )
    }
  val workers: Map<String, DssWorker> =
    blockActors +
      (SEQUENTIAL_OBSERVER_ID to observer) +
      listOfNotNull(visualizer).associateBy { it.id }

  blockActors.values.forEach { it.start() }

  // Round-robin, so a self-feeding loop block can't starve the others
  fun hasWorkLeft() =
    !observer.shutdownRequested() ||
      inboxes.any { (id, queue) -> !workers.getValue(id).shutdownRequested() && queue.isNotEmpty() }
  while (hasWorkLeft()) {
    var processedAny = false
    for ((id, queue) in inboxes) {
      val worker = workers.getValue(id)
      if (worker.shutdownRequested()) {
        queue.clear()
        continue
      }
      val message = queue.poll() ?: continue
      processedAny = true
      worker.processOneMessage(message)
    }
    if (!processedAny && !observer.shutdownRequested()) {
      broadcaster.broadcastToAll(DssResultMessage(SEQUENTIAL_EXECUTOR_ID, DssResult.SAFE))
    }
  }

  return observer.verdict()
}
