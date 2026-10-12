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
 * A participant in the DSS actor network (plan §2). Every actor decides on its own how to answer a
 * received message, and how to route whatever it produces - see [DssBlockActor] and
 * [DssObserverActor] for the two confirmed roles.
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
 * Base [DssActor] loop: block on the next message, process it, route the response, repeat until
 * [shutdownRequested]. [connection.active] is marked around processing (not just while blocked on
 * the queue) to close the quiescence-detection race [DssThreadMonitor] guards against - a thread
 * that has just dequeued its last message but hasn't finished reacting to it yet must not be
 * mistaken for idle.
 *
 * A [processMessage]/[broadcast] failure broadcasts a [DssExceptionMessage] and ends this actor's
 * loop, rather than letting the exception kill the thread silently - not a concern with the stub
 * workers this was first validated against (plan step 4), but real analysis (build-order step 5+)
 * can genuinely fail (solver issues, unexpected states), and a silently-dead thread would otherwise
 * hang the rest of the network forever waiting on messages that will never come. Goes through
 * [DssConnection.broadcaster] directly rather than this actor's own [broadcast] override, since
 * that override may have its own constraints (e.g. [DssObserverActor] asserts it never produces a
 * response at all) that a failure path should not be tripped up by.
 */
abstract class DssWorker(override val id: String) : DssActor {

  /**
   * Processes exactly one already-received [message], routing the response and catching failures
   * the same way [run]'s loop does. Returns `false` if [message] itself caused a failure (an
   * [DssExceptionMessage] has already been broadcast, and this actor should stop) - `true`
   * otherwise. Exposed separately from [run] so a non-threaded executor (build-order step 6's
   * sequential/single-worker executor) can drive this actor message-by-message without a dedicated
   * [Thread].
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
