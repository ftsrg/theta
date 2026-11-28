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

/** CPAchecker's `NO_DECOMPOSITION`: exits at the last dead end a BFS from the entry finds. */
object SingleBlockDecomposition : DssBlockDecomposition {

  override fun decompose(procedure: XcfaProcedure): BlockGraph {
    var lastLocation: XcfaLocation? = null
    val edges = linkedSetOf<XcfaEdge>()
    val seen = linkedSetOf<XcfaLocation>()
    val waitlist = ArrayDeque(listOf(procedure.initLoc))
    while (waitlist.isNotEmpty()) {
      val current = waitlist.removeFirst()
      if (!seen.add(current)) continue
      if (current.outgoingEdges.isEmpty()) lastLocation = current
      for (edge in current.outgoingEdges) {
        edges += edge
        waitlist += edge.target
      }
    }
    checkNotNull(lastLocation) { "Procedure ${procedure.name} has no location without successors" }
    // Not wired by locations: an edgeless procedure's exit is its entry, which would make SB1 its
    // own predecessor and leave the graph without a root
    return BlockGraph(
      setOf(
        Block(
          id = "SB1",
          initialLocation = procedure.initLoc,
          finalLocation = lastLocation,
          locations = seen,
          edges = edges,
        )
      )
    )
  }
}
