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

import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * [MergeBlockDecomposition], then self-loop blocks are absorbed into neighbours, to a fixpoint.
 * With a [portBlockLimit], a loop with several neighbours on both sides is absorbed into all those
 * it is entered from, as port blocks (see [collapseToPortBlocks]).
 */
class SelfLoopAbsorbingDecomposition(
  private val targetBlockCount: Int = DEFAULT_TARGET_BLOCK_COUNT,
  private val largestHorizontalMerge: Int = NO_MERGE_LIMIT,
  private val allowSingleBlockDecomposition: Boolean = false,
  private val linearDecomposition: DssBlockDecomposition = LinearBlockDecomposition(),
  private val portBlockLimit: Int = NO_PORT_BLOCKS,
) : DssBlockDecomposition {

  override fun decompose(procedure: XcfaProcedure): BlockGraph {
    var current =
      MergeBlockDecomposition(
          targetBlockCount,
          largestHorizontalMerge,
          allowSingleBlockDecomposition,
          linearDecomposition,
        )
        .decompose(procedure)
    var rounds = 0
    while (true) {
      // Merging may re-form loops of port blocks; past this many rounds, single hosts end it
      val ports = if (rounds++ < MAX_PORT_ROUNDS) portBlockLimit else NO_PORT_BLOCKS
      val absorbed = absorbSelfLoops(current, ports)
      if (absorbed === current) return current
      current = mergeToTargetBlockCount(absorbed, targetBlockCount, largestHorizontalMerge)
    }
  }
}

private const val MAX_PORT_ROUNDS = 64

/**
 * Into the one other block ending (else starting) at the head; otherwise, with a [portBlockLimit],
 * into the port blocks of the loops and every block ending at the head, else left alone.
 */
fun absorbSelfLoops(blockGraph: BlockGraph, portBlockLimit: Int = NO_PORT_BLOCKS): BlockGraph {
  var nextId =
    blockGraph.blocks
      .mapNotNull { it.id.removePrefix(ABSORBED_PREFIX).toIntOrNull() }
      .maxOrNull()
      ?.plus(1) ?: 0
  var current = blockGraph
  while (true) {
    current =
      absorbFirstSelfLoop(current, "$ABSORBED_PREFIX${nextId}", portBlockLimit) ?: return current
    nextId++
  }
}

private const val ABSORBED_PREFIX = "ML"

private fun absorbFirstSelfLoop(
  blockGraph: BlockGraph,
  id: String,
  portBlockLimit: Int,
): BlockGraph? {
  val loopHeads =
    blockGraph.blocks
      .filter { it.id in it.successorIds }
      .sortedBy { it.id }
      .map { it.initialLocation }
      .distinct()
  for (loopHead in loopHeads) {
    val loops =
      blockGraph.blocks.filter { it.initialLocation == loopHead && it.finalLocation == loopHead }
    val entering = blockGraph.blocks.filter { it.finalLocation == loopHead && it !in loops }
    val leaving = blockGraph.blocks.filter { it.initialLocation == loopHead && it !in loops }
    val host = entering.singleOrNull() ?: leaving.singleOrNull()
    if (host == null) {
      if (portBlockLimit <= 0) continue
      val prefix = "$PORT_PREFIX${nextCollapsedIndex(blockGraph)}"
      val region = loops.mapTo(linkedSetOf()) { it.id }
      return collapseToPortBlocks(blockGraph, region, prefix, portBlockLimit, maxGrowth = 1)
        ?: continue
    }
    val absorbed =
      Block(
        id = id,
        initialLocation = host.initialLocation,
        finalLocation = host.finalLocation,
        locations = loops.flatMapTo(host.locations.toMutableSet()) { it.locations },
        edges = loops.flatMapTo(host.edges.toMutableSet()) { it.edges },
      )
    return BlockGraph.fromBlocksWithoutEdges(blockGraph.blocks - loops.toSet() - host + absorbed)
  }
  return null
}
