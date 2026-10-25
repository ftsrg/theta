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

import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/** CPAchecker's `LINEAR_DECOMPOSITION`: a block ends at every branch, join or dead end. */
class LinearBlockDecomposition(
  private val isBlockEnd: (XcfaLocation) -> Boolean = ::defaultIsBlockEnd
) : DssBlockDecomposition {

  override fun decompose(procedure: XcfaProcedure): BlockGraph {
    val blocks = mutableListOf<Block>()
    val visitedEdges = mutableSetOf<XcfaEdge>()
    var nextId = 0

    val stack = ArrayDeque<Pair<XcfaEdge, Chain>>()
    for (edge in procedure.initLoc.outgoingEdges) {
      stack.addLast(edge to Chain(procedure.initLoc))
    }

    while (stack.isNotEmpty()) {
      val (edge, chain) = stack.removeLast()
      if (!visitedEdges.add(edge)) continue

      chain.locations.add(edge.source)
      chain.locations.add(edge.target)
      chain.edges.add(edge)

      if (isBlockEnd(edge.target)) {
        blocks.add(
          Block(
            id = "L${nextId++}",
            initialLocation = chain.initialLocation,
            finalLocation = edge.target,
            locations = chain.locations,
            edges = chain.edges,
          )
        )
        for (next in edge.target.outgoingEdges) {
          stack.addLast(next to Chain(edge.target))
        }
      } else {
        stack.addLast(edge.target.outgoingEdges.single() to chain)
      }
    }

    return BlockGraph.fromBlocksWithoutEdges(blocks)
  }

  private class Chain(val initialLocation: XcfaLocation) {

    val locations: MutableSet<XcfaLocation> = mutableSetOf(initialLocation)
    val edges: MutableSet<XcfaEdge> = mutableSetOf()
  }

  companion object {

    fun defaultIsBlockEnd(location: XcfaLocation): Boolean =
      location.incomingEdges.size != 1 || location.outgoingEdges.size != 1
  }
}
