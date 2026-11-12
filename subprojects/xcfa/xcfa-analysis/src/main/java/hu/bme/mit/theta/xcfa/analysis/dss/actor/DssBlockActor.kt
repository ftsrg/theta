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

/** CPAchecker's `DssAnalysisWorker`: routes the messages of one block's [behavior]. */
class DssBlockActor(
  private var block: Block,
  override val connection: DssConnection,
  private val behavior: DssBlockBehavior,
) : DssWorker(block.id) {

  private var shutdown = false

  override fun shutdownRequested(): Boolean = shutdown

  /** A cut replaced this block: it handles no more messages, and sends no statistics. */
  fun retire() {
    shutdown = true
  }

  /** A cut replaced the neighbor [oldId] by [replacements]: [newBlock] has the new neighbors. */
  fun neighborReplaced(oldId: String, newBlock: Block, replacements: Set<String>) {
    block = newBlock
    behavior.onNeighborReplaced(oldId, newBlock, replacements)
  }

  override fun processMessage(message: DssMessage): Collection<DssMessage> =
    when (message.type) {
      DssMessageType.POST_CONDITION -> behavior.onPostCondition(message as DssPostConditionMessage)
      DssMessageType.VIOLATION_CONDITION ->
        behavior.onViolationCondition(message as DssViolationConditionMessage)
      DssMessageType.RESTRICTION -> behavior.onRestriction(message as DssRestrictionMessage)
      DssMessageType.CONJECTURE -> behavior.onConjecture(message as DssConjectureMessage)
      DssMessageType.MAY_VIOLATION -> behavior.onMayViolation(message as DssMayViolationMessage)
      DssMessageType.CONJECTURE_FAILED -> emptyList()
      DssMessageType.EXCEPTION,
      DssMessageType.RESULT -> {
        shutdown = true
        listOf(DssStatisticsMessage(id, behavior.statistics()))
      }
      DssMessageType.STATISTIC -> emptyList()
    }

  override fun broadcast(messages: Collection<DssMessage>) {
    val broadcaster = connection.broadcaster
    for (message in messages) {
      when (message.type) {
        DssMessageType.POST_CONDITION -> {
          broadcaster.broadcastToObserver(message)
          if (!(message as DssPostConditionMessage).observerOnly) {
            broadcaster.broadcastToIds(message, block.successorIds)
          }
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
        DssMessageType.MAY_VIOLATION -> {
          // Never a verdict: a root reaching a conjecture's condition reports CONJECTURE_FAILED
          check(!block.isRoot) { "Root ${block.id} cannot send may violations: $message" }
          broadcaster.broadcastToObserver(message)
          broadcaster.broadcastToIds(message, block.predecessorIds)
        }
        DssMessageType.CONJECTURE_FAILED -> broadcaster.broadcastToObserver(message)
        DssMessageType.RESTRICTION,
        DssMessageType.CONJECTURE ->
          error("Block ${block.id} cannot send ${message.type} messages: $message")
      }
    }
  }

  fun start(): Boolean {
    // Like processOneMessage: a capped initial analysis may wait for a permit without looking idle
    connection.active.add(id)
    return try {
      broadcast(behavior.initialMessages())
      true
    } catch (e: Throwable) { // CPAchecker catches `Exception | Error` here, too
      // True if a cut absorbed it, so that the other blocks still start
      connection.reportFailure(DssExceptionMessage(id, e))
    } finally {
      connection.active.remove(id)
    }
  }

  override fun run() {
    if (!start()) return
    super.run()
  }
}
