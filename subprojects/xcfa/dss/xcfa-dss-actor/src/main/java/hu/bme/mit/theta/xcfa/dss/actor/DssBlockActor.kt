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

/** CPAchecker's `DssAnalysisWorker`: routes the messages of one block's [behavior]. */
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
            // No shutdown yet: the RESULT must come back through processMessage to emit the
            // STATISTIC the observer waits on.
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

  fun start(): Boolean =
    try {
      broadcast(behavior.initialMessages())
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
