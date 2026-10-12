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

import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * Theta-only decomposition (no CPAchecker counterpart): [MergeBlockDecomposition], then every
 * self-loop block is absorbed into a neighbour ([absorbSelfLoops]) so that the loop runs inside one
 * block analysis instead of as messages a block keeps sending to itself. Absorbing an inner loop
 * can make an outer loop a self loop, so merging and absorbing alternate until neither changes the
 * graph.
 */
class SelfLoopAbsorbingDecomposition(
  private val targetBlockCount: Int = DEFAULT_TARGET_BLOCK_COUNT,
  private val largestHorizontalMerge: Int = NO_MERGE_LIMIT,
  private val allowSingleBlockDecomposition: Boolean = false,
  private val linearDecomposition: DssBlockDecomposition = LinearBlockDecomposition(),
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
    while (true) {
      val absorbed = absorbSelfLoops(current)
      if (absorbed === current) return current
      current = mergeToTargetBlockCount(absorbed, targetBlockCount, largestHorizontalMerge)
    }
  }
}

/**
 * Absorbs the self-loop blocks of [blockGraph] (blocks whose entry and exit are the same loop head
 * `h`) into a neighbouring block `ML<n>`, until no self loop can be absorbed. All self loops at `h`
 * go into the single other block ending at `h` (the loop is entered from it, and its exit `h` then
 * yields the loop invariant as postcondition), or else into the single other block starting at `h`.
 * A loop head with several of both is left alone, since absorbing would have to duplicate the loop.
 *
 * Returns [blockGraph] itself when nothing was absorbed. Blocks are wired by location, as in
 * [BlockGraph.fromBlocksWithoutEdges], so merging keeps every other block's connections.
 */
fun absorbSelfLoops(blockGraph: BlockGraph): BlockGraph {
  var nextId =
    blockGraph.blocks
      .mapNotNull { it.id.removePrefix(ABSORBED_PREFIX).toIntOrNull() }
      .maxOrNull()
      ?.plus(1) ?: 0
  var current = blockGraph
  while (true) {
    current = absorbFirstSelfLoop(current, "$ABSORBED_PREFIX${nextId}") ?: return current
    nextId++
  }
}

private const val ABSORBED_PREFIX = "ML"

private fun absorbFirstSelfLoop(blockGraph: BlockGraph, id: String): BlockGraph? {
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
    val host = entering.singleOrNull() ?: leaving.singleOrNull() ?: continue
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
