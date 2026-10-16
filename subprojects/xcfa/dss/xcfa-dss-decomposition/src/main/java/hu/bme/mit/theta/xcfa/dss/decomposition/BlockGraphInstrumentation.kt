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

import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * Gives each non-dead-end block its own abstraction point ([Block.violationConditionLocation]) via
 * a no-op ghost edge to a fresh location (CPAchecker's `instrumentCFA`); `xcfa-cli` doesn't run it.
 */
object BlockGraphInstrumentation {

  data class Modification(val procedure: XcfaProcedure, val blockGraph: BlockGraph)

  fun instrumentForAbstraction(procedure: XcfaProcedure, blockGraph: BlockGraph): Modification {
    // CPAchecker's BlockGraphModification.instrumentCFA leaves a single-block graph unchanged.
    if (blockGraph.blocks.size == 1) {
      return Modification(procedure, blockGraph)
    }
    // Mutates the existing locations in place, so this must run after decomposition and merging:
    // re-decomposing an instrumented procedure would treat the ghost edges as real CFG structure.
    val ghostEdgeByFinalLocation = mutableMapOf<XcfaLocation, XcfaEdge>()

    for (finalLocation in blockGraph.blocks.map(Block::finalLocation).toSet()) {
      if (finalLocation.outgoingEdges.isEmpty()) {
        continue
      }
      val ghostLocation = XcfaLocation("${finalLocation.name}__ghost", metadata = GhostEdgeMetadata)
      val ghostEdge = XcfaEdge(finalLocation, ghostLocation, NopLabel, GhostEdgeMetadata)
      finalLocation.outgoingEdges.add(ghostEdge)
      ghostLocation.incomingEdges.add(ghostEdge)
      ghostEdgeByFinalLocation[finalLocation] = ghostEdge
    }

    val instrumentedBlocks =
      blockGraph.blocks.map { block ->
        val ghostEdge = ghostEdgeByFinalLocation[block.finalLocation] ?: return@map block
        block.copy(
          locations = block.locations + ghostEdge.target,
          edges = block.edges + ghostEdge,
          violationConditionLocation = ghostEdge.target,
        )
      }

    val instrumentedProcedure =
      procedure.copy(
        locs = procedure.locs + ghostEdgeByFinalLocation.values.map { it.target },
        edges = procedure.edges + ghostEdgeByFinalLocation.values,
      )

    return Modification(instrumentedProcedure, BlockGraph(instrumentedBlocks.toSet()))
  }
}
