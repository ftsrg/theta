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

interface DssActor : Runnable {

  val id: String

  val connection: DssConnection

  fun processMessage(message: DssMessage): Collection<DssMessage>

  fun broadcast(messages: Collection<DssMessage>)

  /** Once true, never goes back to false. */
  fun shutdownRequested(): Boolean

  fun nextMessage(): DssMessage = connection.read()
}

/** A failure is broadcast as a [DssExceptionMessage] instead of hanging the network. */
abstract class DssWorker(override val id: String) : DssActor {

  /** Marks the actor active meanwhile, so [DssThreadMonitor] never sees it idle. */
  fun processOneMessage(message: DssMessage): Boolean {
    connection.active.add(id)
    try {
      broadcast(processMessage(message))
      return true
    } catch (e: Throwable) { // CPAchecker catches `Exception | Error` here, too
      connection.broadcaster.broadcastToAll(DssExceptionMessage(id, e))
      return false
    } finally {
      connection.active.remove(id)
    }
  }

  override fun run() {
    if (shutdownRequested()) return
    while (!shutdownRequested()) {
      if (!processOneMessage(nextMessage())) return
      if (Thread.currentThread().isInterrupted) break
    }
  }
}
