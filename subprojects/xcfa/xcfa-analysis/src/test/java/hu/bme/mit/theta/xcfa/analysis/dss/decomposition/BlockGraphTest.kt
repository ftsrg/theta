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
package hu.bme.mit.theta.xcfa.analysis.dss.decomposition

import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class BlockGraphTest {

  private fun loc(name: String) = XcfaLocation(name, metadata = EmptyMetaData)

  @Test
  fun `fromBlocksWithoutEdges wires a simple two-block chain`() {
    val a = loc("A")
    val b = loc("B")
    val c = loc("C")
    val first = Block("first", a, b, setOf(a, b), emptySet())
    val second = Block("second", b, c, setOf(b, c), emptySet())

    val blockGraph = BlockGraph.fromBlocksWithoutEdges(listOf(first, second))
    blockGraph.checkConsistency()

    val root = blockGraph.root
    assertEquals("first", root.id)
    val successors = blockGraph.successorsOf(root)
    assertEquals(setOf("second"), successors.map { it.id }.toSet())
    assertEquals(
      setOf("first"),
      blockGraph.predecessorsOf(successors.single()).map { it.id }.toSet(),
    )
  }

  @Test
  fun `checkConsistency rejects a one-sided predecessor link`() {
    val a = loc("A")
    val b = loc("B")
    val root = Block("root", a, a, setOf(a), emptySet())
    val x = Block("x", b, b, setOf(b), emptySet(), predecessorIds = setOf("root"))
    val blockGraph = BlockGraph(setOf(root, x))

    val exception =
      assertThrows(IllegalStateException::class.java) { blockGraph.checkConsistency() }
    assertTrue(exception.message!!.contains("x"))
    assertTrue(exception.message!!.contains("root"))
  }

  @Test
  fun `checkConsistency rejects a block that does not contain its own initial location`() {
    val a = loc("A")
    val b = loc("B")
    val broken = Block("broken", a, b, setOf(b), emptySet()) // "A" missing from locations
    val blockGraph = BlockGraph(setOf(broken))

    val exception =
      assertThrows(IllegalStateException::class.java) { blockGraph.checkConsistency() }
    assertTrue(exception.message!!.contains("initial location"))
  }

  @Test
  fun `checkConsistency rejects a block that does not contain its own final location`() {
    val a = loc("A")
    val b = loc("B")
    val broken = Block("broken", a, b, setOf(a), emptySet()) // "B" missing from locations
    val blockGraph = BlockGraph(setOf(broken))

    val exception =
      assertThrows(IllegalStateException::class.java) { blockGraph.checkConsistency() }
    assertTrue(exception.message!!.contains("final location"))
  }

  @Test
  fun `constructing a BlockGraph with two roots fails`() {
    val a = loc("A")
    val b = loc("B")
    val r1 = Block("r1", a, a, setOf(a), emptySet())
    val r2 = Block("r2", b, b, setOf(b), emptySet())

    assertThrows(IllegalStateException::class.java) { BlockGraph(setOf(r1, r2)) }
  }

  @Test
  fun `constructing a BlockGraph with zero roots fails`() {
    val a = loc("A")
    val b = loc("B")
    val x = Block("x", a, b, setOf(a, b), emptySet(), predecessorIds = setOf("y"))
    val y = Block("y", b, a, setOf(a, b), emptySet(), predecessorIds = setOf("x"))

    assertThrows(IllegalStateException::class.java) { BlockGraph(setOf(x, y)) }
  }
}
