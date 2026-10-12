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

import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * Theta-only decomposition (no CPAchecker counterpart): [MergeBlockDecomposition], then every cycle
 * of the block graph - self loops and cycles through many blocks alike - is collapsed into one
 * block ([collapseCycles]), so the block graph is acyclic and every loop runs inside one block
 * analysis. Merging and collapsing alternate until neither changes the graph.
 */
class AcyclicMergeDecomposition(
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
      val collapsed = collapseCycles(current)
      if (collapsed === current) return current
      current = mergeToTargetBlockCount(collapsed, targetBlockCount, largestHorizontalMerge)
    }
  }
}

/**
 * Collapses every cyclic strongly connected component of [blockGraph] into one block `MC<n>`, the
 * smallest component first, until the graph is acyclic. A block needs a single entry and a single
 * exit location, so the region of a component grows until it has them ([collapseRegion]); it can
 * always grow to the whole procedure, which is a valid single block. Collapsing can close a new
 * cycle through blocks outside the region, which a later round collapses.
 *
 * Returns [blockGraph] itself when it is acyclic already.
 */
fun collapseCycles(blockGraph: BlockGraph): BlockGraph {
  var nextId =
    blockGraph.blocks
      .mapNotNull { it.id.removePrefix(COLLAPSED_PREFIX).toIntOrNull() }
      .maxOrNull()
      ?.plus(1) ?: 0
  var current = blockGraph
  while (true) {
    val successors = current.blocks.associate { it.id to it.successorIds }
    val cycle =
      stronglyConnectedComponents(successors)
        .filter { scc -> scc.size > 1 || scc.single().let { it in successors.getValue(it) } }
        .minWithOrNull(compareBy<Set<String>> { it.size }.thenBy { it.min() }) ?: return current
    current = collapseRegion(current, cycle, "$COLLAPSED_PREFIX${nextId++}")
  }
}

private const val COLLAPSED_PREFIX = "MC"

/**
 * Grows [initialRegion] until it has one entry and at most one exit location, then merges it into
 * one block [id]. Several entries add the predecessors, several exits the successors; an entry that
 * is also the exit adds the predecessors (as [absorbSelfLoops] prefers), since a block starting and
 * ending at the same location is extracted with a split head and could not iterate its loop.
 */
private fun collapseRegion(
  blockGraph: BlockGraph,
  initialRegion: Set<String>,
  id: String,
): BlockGraph {
  val byId = blockGraph.blocks.associateBy { it.id }
  val region = initialRegion.toMutableSet()
  while (true) {
    val members = region.map(byId::getValue)
    val entries =
      members
        .filter { it.isRoot || it.predecessorIds.any { p -> p !in region } }
        .mapTo(linkedSetOf()) { it.initialLocation }
    val exits =
      members
        .filter { it.successorIds.any { s -> s !in region } }
        .mapTo(linkedSetOf()) { it.finalLocation }
    val outsidePredecessors =
      members.flatMap { it.predecessorIds }.filterTo(sortedSetOf()) { it !in region }
    val outsideSuccessors =
      members.flatMap { it.successorIds }.filterTo(sortedSetOf()) { it !in region }
    val grow =
      when {
        entries.size > 1 -> outsidePredecessors
        exits.size > 1 -> outsideSuccessors
        entries == exits -> outsidePredecessors.ifEmpty { outsideSuccessors }
        else -> null
      }
    if (grow == null) {
      val entry = checkNotNull(entries.singleOrNull()) { "Region $region has no entry" }
      val absorbed =
        Block(
          id = id,
          initialLocation = entry,
          finalLocation = exits.singleOrNull() ?: deadEndExit(members, entry),
          locations = members.flatMapTo(linkedSetOf()) { it.locations },
          edges = members.flatMapTo(linkedSetOf()) { it.edges },
        )
      return BlockGraph.fromBlocksWithoutEdges(
        blockGraph.blocks.filter { it.id !in region } + absorbed
      )
    }
    check(grow.isNotEmpty()) { "Region $region cannot grow to a single entry and exit" }
    region += grow
  }
}

/**
 * The exit of a region without successors, which only has to be one of its locations: a location
 * without outgoing edges, preferably not an error location (CPAchecker's single block also ends at
 * a dead end), else any location other than [entry].
 */
private fun deadEndExit(members: List<Block>, entry: XcfaLocation): XcfaLocation {
  val locations = members.flatMap { it.locations }.distinct().sortedBy { it.name }
  return locations.filter { it.outgoingEdges.isEmpty() }.minByOrNull { it.error }
    ?: locations.first { it != entry }
}
