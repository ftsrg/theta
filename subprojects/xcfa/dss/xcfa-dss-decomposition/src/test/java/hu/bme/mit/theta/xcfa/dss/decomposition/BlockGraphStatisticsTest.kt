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
package hu.bme.mit.theta.xcfa.dss.decomposition

import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class BlockGraphStatisticsTest {

  private fun loc(name: String) = XcfaLocation(name, metadata = EmptyMetaData)

  @Test
  fun `a chain has no cycles`() {
    val (a, b, c) = listOf(loc("A"), loc("B"), loc("C"))
    val graph =
      BlockGraph.fromBlocksWithoutEdges(
        listOf(
          Block("first", a, b, setOf(a, b), emptySet()),
          Block("second", b, c, setOf(b, c), emptySet()),
        )
      )
    assertEquals(BlockGraphStatistics(2, 1, 0, 0, 0, 1, 1, 1, 2), graph.statistics())
  }

  @Test
  fun `self loops, back-and-forth pairs and cyclic components are counted`() {
    // root: A->B, x: B->C, self: C->C, y: C->D, z: D->C
    val (a, b, c, d) = listOf(loc("A"), loc("B"), loc("C"), loc("D"))
    val graph =
      BlockGraph.fromBlocksWithoutEdges(
        listOf(
          Block("root", a, b, setOf(a, b), emptySet()),
          Block("x", b, c, setOf(b, c), emptySet()),
          Block("self", c, c, setOf(c), emptySet()),
          Block("y", c, d, setOf(c, d), emptySet()),
          Block("z", d, c, setOf(d, c), emptySet()),
        )
      )
    graph.checkConsistency()
    // root->x, x->{self,y}, self->{self,y}, y->z, z->{self,y}: 8 edges; the cycle {self, y, z}.
    assertEquals(
      BlockGraphStatistics(
        blocks = 5,
        edges = 8,
        selfLoops = 1,
        backAndForthPairs = 1,
        cyclicSccs = 1,
        largestScc = 3,
        maxOutDegree = 2,
        maxInDegree = 3,
        maxBlockLocations = 2,
      ),
      graph.statistics(),
    )
  }
}
