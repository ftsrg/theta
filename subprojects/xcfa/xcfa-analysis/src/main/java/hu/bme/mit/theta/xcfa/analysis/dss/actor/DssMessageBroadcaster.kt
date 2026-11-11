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
import java.util.concurrent.ConcurrentHashMap

enum class DssActorRole {
  BLOCK,
  OBSERVER,
}

class DssMessageBroadcaster(
  connections: Map<String, Pair<DssActorRole, BlockingQueue<DssMessage>>>
) {

  private val queuesById = ConcurrentHashMap<String, BlockingQueue<DssMessage>>()

  private val observerQueues: List<BlockingQueue<DssMessage>> =
    connections.values.filter { (role, _) -> role == DssActorRole.OBSERVER }.map { it.second }

  /** The last postcondition and violation condition each sender delivered to its neighbors. */
  private val lastPostConditions = ConcurrentHashMap<String, DssPostConditionMessage>()
  private val lastViolationConditions = ConcurrentHashMap<String, DssViolationConditionMessage>()

  init {
    connections.forEach { (id, roleAndQueue) -> queuesById[id] = roleAndQueue.second }
  }

  /** Adds a block to a running network (a cut block's pieces). */
  fun register(id: String, queue: BlockingQueue<DssMessage>) {
    check(queuesById.putIfAbsent(id, queue) == null) { "Connection already registered: $id" }
  }

  /** Removes a block, with what it last delivered (a block a cut replaced). */
  fun unregister(id: String) {
    queuesById.remove(id)
    lastPostConditions.remove(id)
    lastViolationConditions.remove(id)
  }

  fun lastPostCondition(senderId: String): DssPostConditionMessage? = lastPostConditions[senderId]

  fun lastViolationCondition(senderId: String): DssViolationConditionMessage? =
    lastViolationConditions[senderId]

  fun isEmpty(): Boolean = queuesById.values.all { it.isEmpty() }

  fun isEmpty(ids: Set<String>): Boolean = ids.all { queuesById[it]?.isEmpty() ?: true }

  fun broadcastToIds(message: DssMessage, ids: Set<String>) {
    when (message) {
      is DssPostConditionMessage -> lastPostConditions[message.senderId] = message
      is DssViolationConditionMessage -> lastViolationConditions[message.senderId] = message
      else -> {}
    }
    for (id in ids) {
      val queue = requireNotNull(queuesById[id]) { "No connection found for id: $id" }
      queue.add(message)
    }
  }

  fun broadcastToObserver(message: DssMessage) {
    for (queue in observerQueues) {
      queue.add(message)
    }
  }

  fun broadcastToAll(message: DssMessage) {
    for (queue in queuesById.values) {
      queue.add(message)
    }
  }
}
