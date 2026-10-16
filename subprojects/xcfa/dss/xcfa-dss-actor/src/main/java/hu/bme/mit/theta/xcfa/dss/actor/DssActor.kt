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
 * A participant in the DSS actor network; decides how to answer and route messages itself. See
 * [DssBlockActor] and [DssObserverActor] for the two roles.
 */
interface DssActor : Runnable {

  val id: String

  val connection: DssConnection

  /** Answers a received message with a (possibly empty) collection of responses. */
  fun processMessage(message: DssMessage): Collection<DssMessage>

  /** Routes a collection of produced messages to whichever other actors should receive them. */
  fun broadcast(messages: Collection<DssMessage>)

  /**
   * Whether this actor should stop working. Once true, must never go back to false (matches
   * CPAchecker's confirmed contract for `DssActor#shutdownRequested`).
   */
  fun shutdownRequested(): Boolean

  fun nextMessage(): DssMessage = connection.read()
}

/**
 * Base [DssActor] loop: take, process, route, repeat until [shutdownRequested]. A failure
 * broadcasts a [DssExceptionMessage] and ends the loop instead of silently hanging the network.
 */
abstract class DssWorker(override val id: String) : DssActor {

  /**
   * Processes one received [message], marking this actor [DssConnection.active] meanwhile so
   * [DssThreadMonitor] never sees it as idle. Returns `false` if it failed (the actor should stop).
   */
  fun processOneMessage(message: DssMessage): Boolean {
    connection.active.add(id)
    try {
      broadcast(
        DssTrace.span(
          "msg",
          "actor" to id,
          "type" to message.type,
          "from" to message.senderId,
          outcome = { "out${it.size}" },
        ) {
          processMessage(message)
        }
      )
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
