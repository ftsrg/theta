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

import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * `blk_linear` from the DSS paper: by default ([isBlockEnd]) a block ends at every branch, join or
 * dead end, so each loop body gets its own block (matches CPAchecker's `config/dss.properties`).
 */
class LinearBlockDecomposition(
  private val isBlockEnd: (XcfaLocation) -> Boolean = ::defaultIsBlockEnd
) : DssBlockDecomposition {

  override fun decompose(procedure: XcfaProcedure): BlockGraph {
    val blocks = mutableListOf<Block>()
    val visitedEdges = mutableSetOf<XcfaEdge>()
    var nextId = 0

    // The block-in-progress that a pending edge would continue, if it turns out not to be a block
    // boundary. Threaded explicitly per traversal branch (rather than one shared mutable
    // accumulator) so that branches pending on the stack can never corrupt each other's state.
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
        // Not a boundary means exactly one outgoing edge (see defaultIsBlockEnd): the chain has a
        // unique continuation, so keep accumulating into the same chain.
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
