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

/** Broadcasts `RESULT(SAFE)` once all threads wait and all queues and [active] are empty. */
class DssThreadMonitor(
  private val threadsToMonitor: List<Thread>,
  private val broadcaster: DssMessageBroadcaster,
  private val active: MutableSet<String>,
  private val id: String = "dss-monitor",
  private val pollIntervalMillis: Long = 10,
) : Thread(id) {

  override fun run() {
    while (true) {
      val allWaiting =
        threadsToMonitor.all { it.state == State.WAITING || it.state == State.TIMED_WAITING }

      if (allWaiting && broadcaster.isEmpty() && active.isEmpty()) {
        broadcaster.broadcastToAll(DssResultMessage(id, DssResult.SAFE))
        return
      }

      try {
        sleep(pollIntervalMillis)
      } catch (e: InterruptedException) {
        broadcaster.broadcastToAll(DssExceptionMessage(id, e))
        currentThread().interrupt()
        return
      }
    }
  }
}
