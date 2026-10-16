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
 * A worker for one [Block], routing as CPAchecker's `DssAnalysisWorker`: postconditions forward,
 * violation conditions backward (UNSAFE at the root); results, exceptions and statistics to all.
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
      traceOutgoing(message)
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

  private fun traceOutgoing(message: DssMessage) {
    if (!DssTrace.enabled) return
    when (message) {
      is DssPostConditionMessage ->
        DssTrace.event(
          "pc-out",
          "actor" to id,
          "to" to block.successorIds.size,
          "states" to message.postconditions.size,
          "prec" to message.precision.size,
          *traceContent(message.postcondition),
        )
      is DssViolationConditionMessage ->
        DssTrace.event(
          "vc-out",
          "actor" to id,
          "root" to block.isRoot,
          *traceContent(message.violationCondition),
        )
      else -> {}
    }
  }

  /**
   * Broadcasts [DssBlockBehavior.initialMessages]; returns `false` if that failed (a
   * [DssExceptionMessage] was broadcast). Separate from [run] for the sequential executor.
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
