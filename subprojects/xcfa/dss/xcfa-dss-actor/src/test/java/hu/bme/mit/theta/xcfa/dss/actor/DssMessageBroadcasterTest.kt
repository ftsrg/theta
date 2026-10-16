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

import java.util.concurrent.LinkedBlockingQueue
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/** Deterministic, single-threaded tests of routing plumbing, independent of running actors. */
class DssMessageBroadcasterTest {

  private fun queue() = LinkedBlockingQueue<DssMessage>()

  @Test
  fun `broadcastToIds only reaches the named queues`() {
    val a = queue()
    val b = queue()
    val c = queue()
    val broadcaster =
      DssMessageBroadcaster(
        mapOf(
          "a" to (DssActorRole.BLOCK to a),
          "b" to (DssActorRole.BLOCK to b),
          "c" to (DssActorRole.BLOCK to c),
        )
      )
    val message = DssPostConditionMessage("root")

    broadcaster.broadcastToIds(message, setOf("a", "c"))

    assertEquals(message, a.poll())
    assertTrue(b.isEmpty())
    assertEquals(message, c.poll())
  }

  @Test
  fun `broadcastToObserver only reaches observer-role queues`() {
    val block = queue()
    val observer = queue()
    val broadcaster =
      DssMessageBroadcaster(
        mapOf(
          "block" to (DssActorRole.BLOCK to block),
          "obs" to (DssActorRole.OBSERVER to observer),
        )
      )
    val message = DssPostConditionMessage("block")

    broadcaster.broadcastToObserver(message)

    assertTrue(block.isEmpty())
    assertEquals(message, observer.poll())
  }

  @Test
  fun `broadcastToAll reaches every queue regardless of role`() {
    val block = queue()
    val observer = queue()
    val broadcaster =
      DssMessageBroadcaster(
        mapOf(
          "block" to (DssActorRole.BLOCK to block),
          "obs" to (DssActorRole.OBSERVER to observer),
        )
      )
    val message = DssResultMessage("dss-monitor", DssResult.SAFE)

    broadcaster.broadcastToAll(message)

    assertEquals(message, block.poll())
    assertEquals(message, observer.poll())
  }

  @Test
  fun `isEmpty is true only when every queue is empty`() {
    val a = queue()
    val b = queue()
    val broadcaster =
      DssMessageBroadcaster(
        mapOf("a" to (DssActorRole.BLOCK to a), "b" to (DssActorRole.BLOCK to b))
      )

    assertTrue(broadcaster.isEmpty())

    a.add(DssPostConditionMessage("x"))

    assertTrue(!broadcaster.isEmpty())
  }

  @Test
  fun `broadcastToIds rejects an unknown id`() {
    val a = queue()
    val broadcaster = DssMessageBroadcaster(mapOf("a" to (DssActorRole.BLOCK to a)))

    org.junit.jupiter.api.Assertions.assertThrows(IllegalArgumentException::class.java) {
      broadcaster.broadcastToIds(DssPostConditionMessage("x"), setOf("does-not-exist"))
    }
  }
}
