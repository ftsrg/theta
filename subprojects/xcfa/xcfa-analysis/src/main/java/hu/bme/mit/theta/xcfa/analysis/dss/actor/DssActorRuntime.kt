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
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.LinkedBlockingQueue
import java.util.concurrent.Semaphore

private const val OBSERVER_ID = "__observer__"

private const val VISUALIZER_ID = "__visualizer__"
private const val VISUALIZER_JOIN_TIMEOUT_MILLIS = 10_000L
private const val BLOCK_THREAD_JOIN_TIMEOUT_MILLIS = 10_000L

/**
 * CPAchecker's `MultithreadingDssExecutor`: one thread per block. With [maxParallelBlocks] > 0, at
 * most that many behavior calls run at a time (0: no limit).
 */
fun runDssActors(
  blockGraph: BlockGraph,
  behaviorFor: (Block) -> DssBlockBehavior,
  pollIntervalMillis: Long = 10,
  visualizationLog: MutableList<DssLogEntry>? = null,
  maxParallelBlocks: Int = 0,
): DssResult =
  runDssNetworks(
      listOf(DssNetwork(blockGraph, behaviorFor)),
      pollIntervalMillis = pollIntervalMillis,
      visualizationLog = visualizationLog,
      maxParallelBlocks = maxParallelBlocks,
    )
    .result

private fun monitorId(networks: List<DssNetwork>, index: Int) =
  if (networks.size == 1) "dss-monitor" else "dss-monitor-$index"

/** [runDssActors] for several [networks] at once, each with its own quiescence monitor. */
fun runDssNetworks(
  networks: List<DssNetwork>,
  coordinator: DssCoordinatorFactory? = null,
  pollIntervalMillis: Long = 10,
  visualizationLog: MutableList<DssLogEntry>? = null,
  maxParallelBlocks: Int = 0,
): DssRun {
  checkUniqueBlockIds(networks)
  val separate = networks.size > 1
  val active = ConcurrentHashMap.newKeySet<String>()
  val blockIds = networks.flatMap { it.blockIds }
  val extraIds =
    listOfNotNull(
      VISUALIZER_ID.takeIf { visualizationLog != null },
      COORDINATOR_ID.takeIf { coordinator != null },
    )
  val inboxes =
    (blockIds + OBSERVER_ID + extraIds).associateWith {
      // Arrival order, so the final messages can't end the visualizer's run early
      if (it == VISUALIZER_ID) LinkedBlockingQueue<DssMessage>() else createDssMessageQueue()
    }
  val blockIdSet = blockIds.toSet()
  val connectionsForBroadcaster =
    inboxes.mapValues { (id, queue) ->
      (if (id in blockIdSet) DssActorRole.BLOCK else DssActorRole.OBSERVER) to queue
    }
  val broadcaster = DssMessageBroadcaster(connectionsForBroadcaster)

  val observer =
    DssObserverActor(
      OBSERVER_ID,
      DssConnection(inboxes.getValue(OBSERVER_ID), broadcaster, active),
      blockIds.size,
      if (separate) networks.map { it.blockIds } else emptyList(),
    )
  // Fair, so a block with queued messages can't be starved by busier ones
  val permits = if (maxParallelBlocks > 0) Semaphore(maxParallelBlocks, true) else null
  val blockActors =
    networks.map { network ->
      network.blockGraph.blocks.map { block ->
        DssBlockActor(
          block,
          DssConnection(
            inboxes.getValue(block.id),
            broadcaster,
            active,
            network.blockIds.takeIf { separate },
          ),
          network.behaviorFor(block).let {
            if (permits == null) it else CappedBlockBehavior(it, permits)
          },
        )
      }
    }
  val visualizer =
    visualizationLog?.let {
      DssVisualizationActor(
        VISUALIZER_ID,
        DssConnection(inboxes.getValue(VISUALIZER_ID), broadcaster, active),
        blockIds.size,
        it,
      )
    }
  val coordinatorActor =
    coordinator?.invoke(DssConnection(inboxes.getValue(COORDINATOR_ID), broadcaster, active))

  fun daemon(runnable: Runnable, name: String) =
    Thread(runnable, name).apply {
      isDaemon = true
      start()
    }
  val blockThreads = blockActors.map { actors -> actors.map { daemon(it, it.id) } }
  val visualizerThread = visualizer?.let { daemon(it, it.id) }
  val coordinatorThread = coordinatorActor?.let { daemon(it, it.id) }
  val monitors =
    networks.indices.map { index ->
      DssThreadMonitor(
          blockThreads[index],
          broadcaster,
          active,
          monitorId(networks, index),
          pollIntervalMillis,
          networks[index].blockIds.takeIf { separate },
        )
        .apply {
          isDaemon = true
          start()
        }
    }

  try {
    val result = observer.observe()
    visualizerThread?.join(VISUALIZER_JOIN_TIMEOUT_MILLIS)
    return DssRun(result, networkOf(networks, observer.resultSender) { monitorId(networks, it) })
  } finally {
    // A monitor only stops on its own after SAFE
    monitors.forEach { it.interrupt() }
    blockThreads.flatten().forEach { it.interrupt() }
    visualizerThread?.interrupt()
    coordinatorThread?.interrupt()
    // Leftover solver threads corrupted the solver state of later runs in the same JVM
    blockThreads.flatten().forEach { it.join(BLOCK_THREAD_JOIN_TIMEOUT_MILLIS) }
    coordinatorThread?.join(BLOCK_THREAD_JOIN_TIMEOUT_MILLIS)
    monitors.forEach { it.join(BLOCK_THREAD_JOIN_TIMEOUT_MILLIS) }
  }
}

/**
 * Waiting for a permit happens inside the caller's `active` marker, so it never looks quiescent.
 */
private class CappedBlockBehavior(
  private val behavior: DssBlockBehavior,
  private val permits: Semaphore,
) : DssBlockBehavior by behavior {

  private fun <T> withPermit(analysis: () -> T): T {
    permits.acquire()
    try {
      return analysis()
    } finally {
      permits.release()
    }
  }

  override fun initialMessages() = withPermit { behavior.initialMessages() }

  override fun onPostCondition(message: DssPostConditionMessage) = withPermit {
    behavior.onPostCondition(message)
  }

  override fun onViolationCondition(message: DssViolationConditionMessage) = withPermit {
    behavior.onViolationCondition(message)
  }

  override fun onRestriction(message: DssRestrictionMessage) = withPermit {
    behavior.onRestriction(message)
  }
}
