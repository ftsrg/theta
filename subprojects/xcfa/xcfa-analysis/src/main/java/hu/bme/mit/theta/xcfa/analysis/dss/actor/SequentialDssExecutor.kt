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
import java.util.concurrent.BlockingQueue
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
 *
 * With a [cutter], a block that asks to be cut ([DssBlockCutRequest]) is replaced by its pieces
 * while the others keep their state. That needs one network and no [coordinator] or visualization,
 * which would have to follow the new blocks; otherwise the request fails the network as usual.
 */
fun runDssNetworksSequentially(
  networks: List<DssNetwork>,
  coordinator: DssCoordinatorFactory? = null,
  visualizationLog: MutableList<DssLogEntry>? = null,
  cutter: DssBlockCutter? = null,
): DssRun {
  checkUniqueBlockIds(networks)
  val separate = networks.size > 1
  val cutting = cutter != null && !separate && coordinator == null && visualizationLog == null
  val active = mutableSetOf<String>()
  val blockIds = networks.flatMap { it.blockIds }
  val extraIds =
    listOfNotNull(
      SEQUENTIAL_VISUALIZER_ID.takeIf { visualizationLog != null },
      COORDINATOR_ID.takeIf { coordinator != null },
    )
  val inboxes =
    (blockIds.sorted() + SEQUENTIAL_OBSERVER_ID + extraIds).associateWithTo(
      linkedMapOf<String, BlockingQueue<DssMessage>>()
    ) {
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
  val blockActors = linkedMapOf<String, DssBlockActor>()
  var cutHandler: (String, DssBlockCutRequest) -> Boolean = { _, _ -> false }
  fun connectionOf(id: String, scope: Set<String>?) =
    DssConnection(
      inboxes.getValue(id),
      broadcaster,
      active,
      scope,
      if (cutting) DssCutHandler { blockId, request -> cutHandler(blockId, request) } else null,
    )
  for (network in networks) {
    for (block in network.blockGraph.blocks) {
      blockActors[block.id] =
        DssBlockActor(
          block,
          connectionOf(block.id, network.blockIds.takeIf { separate }),
          network.behaviorFor(block),
        )
    }
  }
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
  require(!separate || coordinatorActor !is DssConjectureActor) {
    "Conjectures need a single network: each network's quiescence leaves the coordinator out"
  }
  val workers = linkedMapOf<String, DssWorker>()
  workers.putAll(blockActors)
  workers[SEQUENTIAL_OBSERVER_ID] = observer
  listOfNotNull(visualizer, coordinatorActor).forEach { workers[it.id] = it }
  // The coordinator's own id may differ from its queue's
  fun workerOf(queueId: String) =
    if (queueId == COORDINATOR_ID) coordinatorActor!! else workers.getValue(queueId)

  // The graph a cutter works on, as the cuts have changed it
  var currentGraph = networks.first().blockGraph
  val pendingStarts = ArrayDeque<String>()
  if (cutting) {
    val network = networks.single()
    cutHandler = handler@{ blockId, _ ->
      val old = currentGraph.blocks.singleOrNull { it.id == blockId } ?: return@handler false
      val cutGraph = cutter!!.cut(currentGraph, blockId) ?: return@handler false
      val oldIds = currentGraph.blocks.mapTo(hashSetOf()) { it.id }
      val pieces = cutGraph.blocks.filter { it.id !in oldIds }
      val neighbors = (old.predecessorIds + old.successorIds) - old.id

      blockActors.remove(blockId)?.retire()
      workers.remove(blockId)
      inboxes.remove(blockId)
      broadcaster.unregister(blockId)
      // What the block sent and is still queued stood for its latest message, which its pieces
      // replace
      neighbors.forEach { id -> inboxes[id]?.removeIf { it.senderId == blockId } }
      for (piece in pieces) {
        val queue = createDssMessageQueue()
        inboxes[piece.id] = queue
        broadcaster.register(piece.id, queue)
        val actor = DssBlockActor(piece, connectionOf(piece.id, null), network.behaviorFor(piece))
        blockActors[piece.id] = actor
        workers[piece.id] = actor
        pendingStarts.add(piece.id)
      }
      for (neighbor in cutGraph.blocks) {
        if (neighbor.id !in neighbors) continue
        val before = currentGraph.blocks.single { it.id == neighbor.id }
        val replacements =
          (neighbor.predecessorIds + neighbor.successorIds) -
            (before.predecessorIds + before.successorIds)
        blockActors.getValue(neighbor.id).neighborReplaced(blockId, neighbor, replacements)
      }
      observer.blockReplaced(blockId, pieces.size)

      // The pieces start as the block did, then hear what its neighbors last said to it
      val entries = pieces.filter { it.initialLocation == old.initialLocation }
      val exits = pieces.filter { it.finalLocation == old.finalLocation }
      for (id in old.predecessorIds - blockId) {
        broadcaster.lastPostCondition(id)?.let { message ->
          entries.forEach { inboxes.getValue(it.id).add(message) }
        }
      }
      for (id in old.successorIds - blockId) {
        broadcaster.lastViolationCondition(id)?.let { message ->
          exits.forEach { inboxes.getValue(it.id).add(message) }
        }
      }
      currentGraph = cutGraph
      true
    }
  }

  // A failed start ends its network (a cut restarts the run), so its other blocks need not start.
  // Every other network must start, or its unstarted blocks would look quiet, that is SAFE.
  val failedStarts = mutableSetOf<Int>()
  fun startPending(): Boolean {
    var startedAny = false
    while (pendingStarts.isNotEmpty()) {
      val id = pendingStarts.removeFirst()
      val actor = blockActors[id] ?: continue
      val index = networks.indexOfFirst { id in it.blockIds }.coerceAtLeast(0)
      if (index in failedStarts) continue
      startedAny = true
      if (!actor.start()) failedStarts += index
    }
    return startedAny
  }
  networks.forEach { pendingStarts.addAll(it.blockIds) }
  startPending()

  // Round-robin, so a self-feeding loop block can't starve the others
  fun hasWorkLeft() =
    !observer.shutdownRequested() ||
      inboxes.any { (id, queue) -> !workerOf(id).shutdownRequested() && queue.isNotEmpty() }
  while (hasWorkLeft()) {
    var processedAny = false
    // A cut changes the inboxes meanwhile
    for ((id, queue) in inboxes.entries.map { it.key to it.value }) {
      if (id !in inboxes) continue
      val worker = workerOf(id)
      if (worker.shutdownRequested()) {
        queue.clear()
        continue
      }
      val message = queue.poll() ?: continue
      processedAny = true
      worker.processOneMessage(message)
    }
    // The pieces of a cut block start
    processedAny = startPending() || processedAny
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
    if (cutting) listOf(currentGraph) else emptyList(),
  )
}
