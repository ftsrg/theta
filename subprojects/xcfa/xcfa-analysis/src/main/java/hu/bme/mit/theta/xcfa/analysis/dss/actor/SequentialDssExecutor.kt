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

import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import java.util.concurrent.LinkedBlockingQueue

private const val SEQUENTIAL_OBSERVER_ID = "__observer__"
private const val SEQUENTIAL_VISUALIZER_ID = "__visualizer__"
private const val SEQUENTIAL_EXECUTOR_ID = "sequential-executor"

/** CPAchecker's `SequentialDssExecutor`: round-robin, SAFE once every queue is empty. */
fun runDssActorsSequentially(
  blockGraph: BlockGraph,
  behaviorFor: (Block) -> DssBlockBehavior,
  visualizationLog: MutableList<DssLogEntry>? = null,
): DssResult =
  runDssNetworksSequentially(listOf(DssNetwork(blockGraph, behaviorFor)), null, visualizationLog)
    .result

private fun executorId(networks: List<DssNetwork>, index: Int) =
  if (networks.size == 1) SEQUENTIAL_EXECUTOR_ID else "$SEQUENTIAL_EXECUTOR_ID-$index"

/**
 * [runDssActorsSequentially] for several [networks]: a network is SAFE once its own queues are
 * empty after a round, unless one of its blocks has shut down (it failed).
 */
fun runDssNetworksSequentially(
  networks: List<DssNetwork>,
  coordinator: DssCoordinatorFactory? = null,
  visualizationLog: MutableList<DssLogEntry>? = null,
): DssRun {
  checkUniqueBlockIds(networks)
  val separate = networks.size > 1
  val active = mutableSetOf<String>()
  val blockIds = networks.flatMap { it.blockIds }
  val extraIds =
    listOfNotNull(
      SEQUENTIAL_VISUALIZER_ID.takeIf { visualizationLog != null },
      COORDINATOR_ID.takeIf { coordinator != null },
    )
  val inboxes =
    (blockIds.sorted() + SEQUENTIAL_OBSERVER_ID + extraIds).associateWith {
      // Arrival order, so the final messages can't end the visualizer's run early
      if (it == SEQUENTIAL_VISUALIZER_ID) LinkedBlockingQueue<DssMessage>()
      else createDssMessageQueue()
    }
  val blockIdSet = blockIds.toSet()
  val connectionsForBroadcaster =
    inboxes.mapValues { (id, queue) ->
      (if (id in blockIdSet) DssActorRole.BLOCK else DssActorRole.OBSERVER) to queue
    }
  val broadcaster = DssMessageBroadcaster(connectionsForBroadcaster)

  val observer =
    DssObserverActor(
      SEQUENTIAL_OBSERVER_ID,
      DssConnection(inboxes.getValue(SEQUENTIAL_OBSERVER_ID), broadcaster, active),
      blockIds.size,
      if (separate) networks.map { it.blockIds } else emptyList(),
    )
  val blockActors =
    networks
      .flatMap { network ->
        network.blockGraph.blocks.map { block ->
          block.id to
            DssBlockActor(
              block,
              DssConnection(
                inboxes.getValue(block.id),
                broadcaster,
                active,
                network.blockIds.takeIf { separate },
              ),
              network.behaviorFor(block),
            )
        }
      }
      .toMap()
  val visualizer =
    visualizationLog?.let {
      DssVisualizationActor(
        SEQUENTIAL_VISUALIZER_ID,
        DssConnection(inboxes.getValue(SEQUENTIAL_VISUALIZER_ID), broadcaster, active),
        blockIds.size,
        it,
      )
    }
  val coordinatorActor =
    coordinator?.invoke(DssConnection(inboxes.getValue(COORDINATOR_ID), broadcaster, active))
  val workers: Map<String, DssWorker> =
    blockActors +
      (SEQUENTIAL_OBSERVER_ID to observer) +
      listOfNotNull(visualizer, coordinatorActor).associateBy { it.id }
  // The coordinator's own id may differ from its queue's
  fun workerOf(queueId: String) =
    if (queueId == COORDINATOR_ID) coordinatorActor!! else workers.getValue(queueId)

  blockActors.values.forEach { it.start() }

  // Round-robin, so a self-feeding loop block can't starve the others
  fun hasWorkLeft() =
    !observer.shutdownRequested() ||
      inboxes.any { (id, queue) -> !workerOf(id).shutdownRequested() && queue.isNotEmpty() }
  while (hasWorkLeft()) {
    var processedAny = false
    for ((id, queue) in inboxes) {
      val worker = workerOf(id)
      if (worker.shutdownRequested()) {
        queue.clear()
        continue
      }
      val message = queue.poll() ?: continue
      processedAny = true
      worker.processOneMessage(message)
    }
    if (observer.shutdownRequested()) continue
    if (!separate) {
      if (!processedAny) {
        broadcaster.broadcastToAll(DssResultMessage(SEQUENTIAL_EXECUTOR_ID, DssResult.SAFE))
      }
      continue
    }
    // A RESULT already sent sits in every live block's queue, so no network looks quiet then
    val quiet =
      networks.indices.firstOrNull { index ->
        val ids = networks[index].blockIds
        ids.none { blockActors.getValue(it).shutdownRequested() } &&
          ids.all { inboxes.getValue(it).isEmpty() }
      }
    if (quiet != null) {
      broadcaster.broadcastToAll(DssResultMessage(executorId(networks, quiet), DssResult.SAFE))
    } else {
      check(processedAny) { "DSS networks stopped without a verdict" }
    }
  }

  return DssRun(
    observer.verdict(),
    networkOf(networks, observer.resultSender) { executorId(networks, it) },
  )
}
