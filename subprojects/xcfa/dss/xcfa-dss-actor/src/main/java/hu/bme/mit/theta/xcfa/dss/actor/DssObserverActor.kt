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

/**
 * Passively collects the verdict (CPAchecker's `DssObserverWorker`); stops once a `RESULT` and all
 * blocks' `STATISTIC`s arrived, in any order, since `broadcastToAll` isn't atomic across queues.
 */
class DssObserverActor(
  id: String,
  override val connection: DssConnection,
  private val numberOfBlocks: Int,
) : DssWorker(id) {

  private var shutdown = false
  private var result: DssResult? = null
  private var failure: Throwable? = null
  private val statsReceivedFrom = mutableSetOf<String>()

  override fun shutdownRequested(): Boolean = shutdown

  override fun processMessage(message: DssMessage): Collection<DssMessage> {
    when (message.type) {
      DssMessageType.RESULT -> result = (message as DssResultMessage).result
      DssMessageType.EXCEPTION -> {
        failure = (message as DssExceptionMessage).error
        shutdown = true
      }
      DssMessageType.STATISTIC -> statsReceivedFrom.add(message.senderId)
      DssMessageType.POST_CONDITION,
      DssMessageType.VIOLATION_CONDITION -> {}
    }
    if (result != null && statsReceivedFrom.size >= numberOfBlocks) {
      shutdown = true
    }
    return emptyList()
  }

  override fun broadcast(messages: Collection<DssMessage>) {
    check(messages.isEmpty()) { "Observer never produces a response, but got: $messages" }
  }

  /** Blocks the calling thread until a final verdict is known. */
  fun observe(): DssResult {
    run()
    return verdict()
  }

  /**
   * The verdict so far, throwing like [observe] if none is known yet. Separate from [observe] for
   * executors that drive [processMessage] directly instead of [run].
   */
  fun verdict(): DssResult {
    failure?.let { throw IllegalStateException(it.message, it) }
    return result ?: error("Analysis finished but no result is present.")
  }
}
