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
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.LinkedBlockingQueue

private const val OBSERVER_ID = "__observer__"

private const val VISUALIZER_ID = "__visualizer__"
private const val VISUALIZER_JOIN_TIMEOUT_MILLIS = 10_000L
private const val BLOCK_THREAD_JOIN_TIMEOUT_MILLIS = 10_000L

/** CPAchecker's `MultithreadingDssExecutor`: one thread per block. */
fun runDssActors(
  blockGraph: BlockGraph,
  behaviorFor: (Block) -> DssBlockBehavior,
  pollIntervalMillis: Long = 10,
  visualizationLog: MutableList<DssLogEntry>? = null,
): DssResult {
  val active = ConcurrentHashMap.newKeySet<String>()
  val extraIds = if (visualizationLog != null) setOf(VISUALIZER_ID) else emptySet()
  val inboxes =
    (blockGraph.blocks.map { it.id } + OBSERVER_ID + extraIds).associateWith {
      // Arrival order, so the final messages can't end the visualizer's run early
      if (it == VISUALIZER_ID) LinkedBlockingQueue<DssMessage>() else createDssMessageQueue()
    }
  val connectionsForBroadcaster =
    inboxes.mapValues { (id, queue) ->
      (if (id == OBSERVER_ID || id == VISUALIZER_ID) DssActorRole.OBSERVER
      else DssActorRole.BLOCK) to queue
    }
  val broadcaster = DssMessageBroadcaster(connectionsForBroadcaster)

  val observer =
    DssObserverActor(
      OBSERVER_ID,
      DssConnection(inboxes.getValue(OBSERVER_ID), broadcaster, active),
      blockGraph.blocks.size,
    )
  val blockActors =
    blockGraph.blocks.map { block ->
      DssBlockActor(
        block,
        DssConnection(inboxes.getValue(block.id), broadcaster, active),
        behaviorFor(block),
      )
    }
  val visualizer =
    visualizationLog?.let {
      DssVisualizationActor(
        VISUALIZER_ID,
        DssConnection(inboxes.getValue(VISUALIZER_ID), broadcaster, active),
        blockGraph.blocks.size,
        it,
      )
    }

  val blockThreads =
    blockActors.map { actor ->
      Thread(actor, actor.id).apply {
        isDaemon = true
        start()
      }
    }
  val visualizerThread =
    visualizer?.let {
      Thread(it, it.id).apply {
        isDaemon = true
        start()
      }
    }
  val monitor =
    DssThreadMonitor(blockThreads, broadcaster, active, pollIntervalMillis = pollIntervalMillis)
      .apply {
        isDaemon = true
        start()
      }

  try {
    val result = observer.observe()
    visualizerThread?.join(VISUALIZER_JOIN_TIMEOUT_MILLIS)
    return result
  } finally {
    // The monitor only stops on its own after SAFE
    monitor.interrupt()
    blockThreads.forEach { it.interrupt() }
    visualizerThread?.interrupt()
    // Leftover solver threads corrupted the solver state of later runs in the same JVM
    blockThreads.forEach { it.join(BLOCK_THREAD_JOIN_TIMEOUT_MILLIS) }
    monitor.join(BLOCK_THREAD_JOIN_TIMEOUT_MILLIS)
  }
}
