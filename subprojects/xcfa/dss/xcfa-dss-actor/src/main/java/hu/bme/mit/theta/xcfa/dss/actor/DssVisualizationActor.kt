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

/** One observed message, tagged with the wall-clock time it was processed at. */
data class DssLogEntry(val timestampMillis: Long, val message: DssMessage)

/**
 * Optional debug observer (CPAchecker's `DssVisualizationWorker`) that records every message it
 * receives into [log], shutting down like [DssObserverActor] so executors can wait for it.
 */
class DssVisualizationActor(
  id: String,
  override val connection: DssConnection,
  private val numberOfBlocks: Int,
  private val entries: MutableList<DssLogEntry> = mutableListOf(),
) : DssWorker(id) {

  private var shutdown = false
  private var sawFinalMessage = false
  private val statsReceivedFrom = mutableSetOf<String>()

  /** Every message this actor has observed, in receipt order, oldest first. */
  val log: List<DssLogEntry>
    get() = entries

  override fun shutdownRequested(): Boolean = shutdown

  override fun processMessage(message: DssMessage): Collection<DssMessage> {
    entries.add(DssLogEntry(System.currentTimeMillis(), message))
    when (message.type) {
      DssMessageType.RESULT,
      DssMessageType.EXCEPTION -> sawFinalMessage = true
      DssMessageType.STATISTIC -> statsReceivedFrom.add(message.senderId)
      DssMessageType.POST_CONDITION,
      DssMessageType.VIOLATION_CONDITION -> {}
    }
    if (sawFinalMessage && statsReceivedFrom.size >= numberOfBlocks) {
      shutdown = true
    }
    return emptyList()
  }

  override fun broadcast(messages: Collection<DssMessage>) {
    check(messages.isEmpty()) { "The visualizer never produces a response, but got: $messages" }
  }
}
