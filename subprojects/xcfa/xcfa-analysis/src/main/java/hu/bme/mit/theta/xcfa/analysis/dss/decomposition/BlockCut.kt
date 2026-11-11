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
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import java.util.Optional

/** What cuts a block unless a decomposition is named: two pieces with the fewest edges between. */
val DEFAULT_BLOCK_CUT: DssBlockDecomposition =
  MinCutDecomposition(loopHandling = CutLoopHandling.ABSORB_SELF_LOOPS)

/**
 * [block] in smaller pieces (null if it has no cut), for a block too hard for every checker: the
 * [decomposition] applied to the block alone, as if it were a procedure of its own. The pieces keep
 * all the paths of the block:
 * - they share no edge and cover the block's reachable ones, and take every edge out of a location
 *   they pass through;
 * - one ends at the block's exit if a successor starts there, and none passes through the exit or
 *   (unless the block is the root) the entry;
 * - a root block keeps its single root piece, as a block graph has exactly one root.
 *
 * A decomposition that gives one piece, or cannot handle the block, gives no cut.
 */
fun cutBlock(block: Block, decomposition: DssBlockDecomposition = DEFAULT_BLOCK_CUT): List<Block>? {
  val reachable = reachableEdges(block)
  if (reachable.size < 2) return null
  val clone = cloneBlock(block, edges = reachable)
  // A decomposition wants one way in and a dead end out, but an entry can branch, and a loop can
  // run through the exit: the block gets an edge to enter and to leave by, dropped from the pieces
  val enter = clone.entry.takeIf { it.outgoingEdges.size > 1 }?.let(::enteringEdge)
  val leave = clone.exit.takeIf { it.outgoingEdges.isNotEmpty() }?.let(::leavingEdge)
  val added = listOfNotNull(enter, leave)
  val procedure =
    XcfaProcedure(
      name = block.id,
      params = emptyList(),
      vars = emptySet(),
      locs = clone.originalLocations.keys + added.flatMap { listOf(it.source, it.target) },
      edges = clone.edges + added,
      initLoc = enter?.source ?: clone.entry,
      finalLoc = Optional.empty(),
      errorLoc = Optional.empty(),
    )
  val graph =
    try {
      decomposition.decompose(procedure)
    } catch (e: IllegalStateException) {
      return null
    }
  fun originalOf(location: XcfaLocation) =
    when (location) {
      enter?.source -> block.initialLocation
      leave?.target -> block.finalLocation
      else -> clone.originalLocations.getValue(location)
    }
  val pieces =
    graph.blocks
      .map { piece -> piece to piece.edges.filter { it !in added } }
      // What is left of a piece that only enters or leaves the block is nothing
      .filter { (_, edges) -> edges.isNotEmpty() }
      .mapIndexed { index, (piece, edges) ->
        Block(
          id = "${block.id}_$index",
          initialLocation = originalOf(piece.initialLocation),
          finalLocation = originalOf(piece.finalLocation),
          locations = piece.locations.mapTo(linkedSetOf(), ::originalOf),
          edges = edges.mapTo(linkedSetOf()) { clone.originalEdges.getValue(it) },
        )
      }
  return pieces.takeIf { it.size >= 2 && keepsPaths(block, reachable, it) }
}

private fun connect(source: XcfaLocation, target: XcfaLocation): XcfaEdge =
  XcfaEdge(source, target, SequenceLabel(emptyList()), EmptyMetaData).also {
    source.outgoingEdges.add(it)
    target.incomingEdges.add(it)
  }

/** An edge from a new location to [entry], which stands for entering the block. */
private fun enteringEdge(entry: XcfaLocation) =
  connect(XcfaLocation("${entry.name}__in", metadata = EmptyMetaData), entry)

/** An edge from [exit] to a new dead end, which stands for leaving the block. */
private fun leavingEdge(exit: XcfaLocation) =
  connect(exit, XcfaLocation("${exit.name}__out", metadata = EmptyMetaData))

/** The block's edges reachable from its entry. */
private fun reachableEdges(block: Block): Set<XcfaEdge> {
  val bySource = block.edges.groupBy { it.source }
  val edges = linkedSetOf<XcfaEdge>()
  val seen = hashSetOf(block.initialLocation)
  val waitlist = ArrayDeque(listOf(block.initialLocation))
  while (waitlist.isNotEmpty()) {
    for (edge in bySource[waitlist.removeFirst()].orEmpty()) {
      edges += edge
      if (seen.add(edge.target)) waitlist.addLast(edge.target)
    }
  }
  return edges
}

private fun keepsPaths(block: Block, reachable: Set<XcfaEdge>, pieces: List<Block>): Boolean {
  if (pieces.sumOf { it.edges.size } != reachable.size) return false
  if (pieces.flatMapTo(hashSetOf()) { it.edges } != reachable) return false
  // Where the successors start, and where a loop block's states come back to its entry
  val exit = block.finalLocation.takeIf { block.successorIds.isNotEmpty() }
  val entry = block.initialLocation.takeUnless { block.isRoot }
  val bySource = reachable.groupBy { it.source }
  for (piece in pieces) {
    for (location in piece.locations - piece.initialLocation - piece.finalLocation) {
      if (location == exit || location == entry) return false
      if (!piece.edges.containsAll(bySource[location].orEmpty())) return false
    }
  }
  if (exit != null && pieces.none { it.finalLocation == exit }) return false
  if (block.isRoot) {
    if (pieces.count { it.initialLocation == block.initialLocation } != 1) return false
    if (pieces.any { it.finalLocation == block.initialLocation }) return false
  }
  return true
}

/** This graph with block [id] replaced by its [cutBlock] pieces, or null if it has no cut. */
fun BlockGraph.cut(
  id: String,
  decomposition: DssBlockDecomposition = DEFAULT_BLOCK_CUT,
): BlockGraph? {
  val block = blocks.singleOrNull { it.id == id } ?: error("BlockGraph has no block with id '$id'")
  val pieces = cutBlock(block, decomposition) ?: return null
  val entries = pieces.filter { it.initialLocation == block.initialLocation }.map { it.id }
  val exits = pieces.filter { it.finalLocation == block.finalLocation }.map { it.id }
  val outerPredecessors = block.predecessorIds - id
  val outerSuccessors = block.successorIds - id
  val wired =
    pieces.map { piece ->
      piece.copy(
        predecessorIds =
          pieces.filter { it.finalLocation == piece.initialLocation }.map { it.id }.toSet() +
            if (piece.initialLocation == block.initialLocation) outerPredecessors else emptySet(),
        successorIds =
          pieces.filter { it.initialLocation == piece.finalLocation }.map { it.id }.toSet() +
            if (piece.finalLocation == block.finalLocation) outerSuccessors else emptySet(),
      )
    }
  val others =
    (blocks - block).map { other ->
      other.copy(
        predecessorIds =
          other.predecessorIds.flatMapTo(linkedSetOf()) { if (it == id) exits else listOf(it) },
        successorIds =
          other.successorIds.flatMapTo(linkedSetOf()) { if (it == id) entries else listOf(it) },
      )
    }
  return BlockGraph((others + wired).toSet()).also { it.checkConsistency() }
}
