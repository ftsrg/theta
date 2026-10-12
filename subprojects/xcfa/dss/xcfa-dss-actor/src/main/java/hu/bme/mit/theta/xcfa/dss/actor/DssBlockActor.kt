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

/**
 * A worker responsible for one [Block]. Delegates the actual analysis reaction to a
 * [DssBlockBehavior] (a stub for now - see [EchoBlockAnalysis]) and owns exactly the routing and
 * termination logic confirmed from CPAchecker's `DssAnalysisWorker.broadcast` (plan §2):
 * - `POST_CONDITION` goes to the observer and to [Block.successorIds] only - forward along the
 *   block graph.
 * - `VIOLATION_CONDITION`: if this block has no predecessors (it is the root), that is an
 *   immediate, local short-circuit - broadcast `RESULT(UNSAFE)` to everyone, no need to wait for
 *   [DssThreadMonitor] to notice anything. This worker does *not* shut down at that point, though:
 *   it still needs to receive its own broadcast `RESULT` back through the normal loop and answer it
 *   (see below), like every other worker does. Otherwise `VIOLATION_CONDITION` goes to the observer
 *   and to [Block.predecessorIds] only - backward along the block graph.
 * - `EXCEPTION`/`RESULT` received: this worker shuts down and answers with its own `STATISTIC`.
 * - `EXCEPTION`/`RESULT`/`STATISTIC` about to be *sent* (whether self-triggered above or in answer
 *   to one just received): goes to everyone.
 *
 * On startup, broadcasts [DssBlockBehavior.initialMessages] before entering the normal receive
 * loop - every block runs its own initial analysis, not just the root (matches CPAchecker: a block
 * with no incoming information yet still explores from its own most-general entry state).
 */
class DssBlockActor(
  private val block: Block,
  override val connection: DssConnection,
  private val behavior: DssBlockBehavior,
) : DssWorker(block.id) {

  private var shutdown = false

  override fun shutdownRequested(): Boolean = shutdown

  override fun processMessage(message: DssMessage): Collection<DssMessage> =
    when (message.type) {
      DssMessageType.POST_CONDITION -> behavior.onPostCondition(message as DssPostConditionMessage)
      DssMessageType.VIOLATION_CONDITION ->
        behavior.onViolationCondition(message as DssViolationConditionMessage)
      DssMessageType.EXCEPTION,
      DssMessageType.RESULT -> {
        shutdown = true
        listOf(DssStatisticsMessage(id))
      }
      DssMessageType.STATISTIC -> emptyList()
    }

  override fun broadcast(messages: Collection<DssMessage>) {
    val broadcaster = connection.broadcaster
    for (message in messages) {
      when (message.type) {
        DssMessageType.POST_CONDITION -> {
          broadcaster.broadcastToObserver(message)
          broadcaster.broadcastToIds(message, block.successorIds)
        }
        DssMessageType.VIOLATION_CONDITION -> {
          if (block.isRoot) {
            // Not `shutdown = true` here: this worker still needs to receive its own broadcast
            // RESULT message back through the normal loop (see processMessage) to emit the
            // STATISTIC message the observer waits on. Shutting down early would leave that
            // message permanently unconsumed and hang the whole run.
            broadcaster.broadcastToAll(DssResultMessage(id, DssResult.UNSAFE))
          } else {
            broadcaster.broadcastToObserver(message)
            broadcaster.broadcastToIds(message, block.predecessorIds)
          }
        }
        DssMessageType.EXCEPTION,
        DssMessageType.RESULT,
        DssMessageType.STATISTIC -> {
          broadcaster.broadcastToAll(message)
          shutdown = true
        }
      }
    }
  }

  /**
   * Broadcasts this block's initial analysis messages ([DssBlockBehavior.initialMessages]),
   * catching a failure the same way normal message processing does. Returns `false` if the initial
   * analysis itself failed (an [DssExceptionMessage] has already been broadcast). Exposed
   * separately from [run] so a non-threaded executor (build-order step 6's sequential/single-worker
   * executor) can drive this actor without a dedicated [Thread].
   */
  fun start(): Boolean =
    try {
      broadcast(
        DssTrace.span("init", "actor" to id, outcome = { "out${it.size}" }) {
          behavior.initialMessages()
        }
      )
      true
    } catch (e: Throwable) { // CPAchecker catches `Exception | Error` here, too
      connection.broadcaster.broadcastToAll(DssExceptionMessage(id, e))
      false
    }

  override fun run() {
    if (!start()) return
    super.run()
  }
}
