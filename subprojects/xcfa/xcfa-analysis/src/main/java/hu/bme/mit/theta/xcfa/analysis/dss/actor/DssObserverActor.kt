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

/**
 * CPAchecker's `DssObserverWorker`: waits for a `RESULT` and every block's `STATISTIC`. With
 * several [networks], a failure ends only its own network, and two different `RESULT`s fail the
 * run.
 */
class DssObserverActor(
  id: String,
  override val connection: DssConnection,
  private var numberOfBlocks: Int,
  private val networks: List<Set<String>> = emptyList(),
) : DssWorker(id) {

  private var shutdown = false
  private var result: DssResult? = null
  private var failure: Throwable? = null
  private var disagreement: Throwable? = null
  private val failedNetworks = mutableSetOf<Int>()
  private val statsReceivedFrom = mutableSetOf<String>()

  /** The sender of the first `RESULT`. */
  var resultSender: String? = null
    private set

  override fun shutdownRequested(): Boolean = shutdown

  /** A cut replaced block [oldId] by [pieces]: their statistics are waited for instead. */
  fun blockReplaced(oldId: String, pieces: Int) {
    numberOfBlocks += pieces - 1
    statsReceivedFrom.remove(oldId)
  }

  override fun processMessage(message: DssMessage): Collection<DssMessage> {
    when (message.type) {
      DssMessageType.RESULT -> {
        val received = (message as DssResultMessage).result
        if (result == null) {
          result = received
          resultSender = message.senderId
        } else if (received != result) {
          disagreement =
            IllegalStateException(
              "DSS networks disagree: $result from $resultSender, $received from ${message.senderId}"
            )
          shutdown = true
        }
      }
      DssMessageType.EXCEPTION -> {
        if (failure == null) failure = (message as DssExceptionMessage).error
        val network = networks.indexOfFirst { message.senderId in it }
        if (networks.size <= 1 || network < 0) shutdown = true
        else {
          failedNetworks += network
          if (failedNetworks.size == networks.size) shutdown = true
        }
      }
      DssMessageType.STATISTIC -> statsReceivedFrom.add(message.senderId)
      DssMessageType.POST_CONDITION,
      DssMessageType.VIOLATION_CONDITION,
      DssMessageType.RESTRICTION,
      DssMessageType.CONJECTURE,
      DssMessageType.MAY_VIOLATION,
      DssMessageType.CONJECTURE_FAILED -> {}
    }
    if (result != null && allStatisticsReceived()) {
      shutdown = true
    }
    return emptyList()
  }

  /** A failed network's failing block never answers, so only the others are waited for. */
  private fun allStatisticsReceived(): Boolean =
    if (networks.size <= 1) statsReceivedFrom.size >= numberOfBlocks
    else
      networks.withIndex().all { (index, ids) ->
        index in failedNetworks || statsReceivedFrom.containsAll(ids)
      }

  override fun broadcast(messages: Collection<DssMessage>) {
    check(messages.isEmpty()) { "Observer never produces a response, but got: $messages" }
  }

  fun observe(): DssResult {
    run()
    return verdict()
  }

  fun verdict(): DssResult {
    disagreement?.let { throw it }
    val found = result
    if (networks.size > 1 && found != null) return found
    failure?.let { throw IllegalStateException(it.message, it) }
    return found ?: error("Analysis finished but no result is present.")
  }
}
