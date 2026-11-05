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

import java.util.concurrent.BlockingQueue

/**
 * A failure reaches only the blocks of [failureScope] and the observers, everyone if it is null.
 */
class DssConnection(
  private val inbox: BlockingQueue<DssMessage>,
  val broadcaster: DssMessageBroadcaster,
  val active: MutableSet<String>,
  val failureScope: Set<String>? = null,
) {

  fun read(): DssMessage = inbox.take()

  fun reportFailure(message: DssExceptionMessage) {
    if (failureScope == null) {
      broadcaster.broadcastToAll(message)
    } else {
      broadcaster.broadcastToIds(message, failureScope)
      broadcaster.broadcastToObserver(message)
    }
  }
}
