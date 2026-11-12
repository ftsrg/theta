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

import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssBlockCutRequest
import java.util.concurrent.BlockingQueue

/** Replaces a block that asked to be cut, in place of failing the network. */
fun interface DssCutHandler {

  /** Whether the cut was made; if not, the request fails the network like any exception. */
  fun cut(blockId: String, request: DssBlockCutRequest): Boolean
}

/**
 * A failure reaches only the blocks of [failureScope] and the observers, everyone if it is null. A
 * [DssBlockCutRequest] goes to [cutHandler] first, if there is one.
 */
class DssConnection(
  private val inbox: BlockingQueue<DssMessage>,
  val broadcaster: DssMessageBroadcaster,
  val active: MutableSet<String>,
  val failureScope: Set<String>? = null,
  private val cutHandler: DssCutHandler? = null,
) {

  fun read(): DssMessage = inbox.take()

  /** Returns whether a cut absorbed the failure: then nothing is broadcast. */
  fun reportFailure(message: DssExceptionMessage): Boolean {
    val request =
      generateSequence(message.error) { it.cause }
        .filterIsInstance<DssBlockCutRequest>()
        .firstOrNull()
    if (request != null && cutHandler?.cut(message.senderId, request) == true) return true
    if (failureScope == null) {
      broadcaster.broadcastToAll(message)
    } else {
      broadcaster.broadcastToIds(message, failureScope)
      broadcaster.broadcastToObserver(message)
    }
    return false
  }
}
