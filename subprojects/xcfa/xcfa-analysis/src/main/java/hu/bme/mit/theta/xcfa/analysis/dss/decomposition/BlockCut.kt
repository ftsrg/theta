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

/**
 * [block] in smaller pieces (null if it has no cut), for a block too hard for every checker. It is
 * cut at one more location or at none, and the edges leaving the entry or the cut location start
 * separate pieces wherever they share no location, so a loop head splits into its loop and its
 * exit. As in [MinCutDecomposition], the fewest edges into the cut location win, then the cut whose
 * largest piece is the smallest.
 *
 * Every piece takes all of the block's edges out of each location it passes through, and a piece
 * reaching the block's exit (if a successor starts there) or entry ends there, so the pieces cover
 * exactly the block's paths. A root has no piece ending at its entry and a single one starting
 * there, as a block graph has one root.
 */
fun cutBlock(block: Block, searchBudget: Long = DEFAULT_CUT_SEARCH_BUDGET): List<Block>? =
  BlockCutSearch(block, searchBudget).best()

/** This graph with block [id] replaced by its [cutBlock] pieces, or null if it has no cut. */
fun BlockGraph.cut(id: String): BlockGraph? {
  val block = blocks.singleOrNull { it.id == id } ?: error("BlockGraph has no block with id '$id'")
  val pieces = cutBlock(block) ?: return null
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

private class BlockCutSearch(private val block: Block, private val budget: Long) {

  /** The block's edges reachable from its entry, by source. */
  private val outgoing: Map<XcfaLocation, List<XcfaEdge>> =
    buildMap<XcfaLocation, MutableList<XcfaEdge>> {
      val bySource = block.edges.groupBy { it.source }
      val seen = mutableSetOf(block.initialLocation)
      val waitlist = ArrayDeque(listOf(block.initialLocation))
      while (waitlist.isNotEmpty()) {
        val location = waitlist.removeFirst()
        for (edge in bySource[location].orEmpty()) {
          getOrPut(location) { mutableListOf() }.add(edge)
          if (seen.add(edge.target)) waitlist.addLast(edge.target)
        }
      }
    }

  private val reachableEdges: Set<XcfaEdge> = outgoing.values.flatten().toSet()

  /** Where the block's postcondition goes; without a successor the exit is only a dead end. */
  private val exit: XcfaLocation? = block.finalLocation.takeIf { block.successorIds.isNotEmpty() }

  /** A piece returning to the entry of a loop block hands its states to the entry pieces. */
  private val entry: XcfaLocation? = block.initialLocation.takeUnless { block.isRoot }

  private val candidates: List<XcfaLocation> =
    reachableEdges
      .map { it.target }
      .distinct()
      .filter { it != block.initialLocation && it != block.finalLocation && it in outgoing }
      .sortedBy { it.name }

  private var visits = 0L

  private class Walk(
    val edges: MutableSet<XcfaEdge> = linkedSetOf(),
    val locations: MutableSet<XcfaLocation> = linkedSetOf(),
    /** Passed through, i.e. all of their edges taken. */
    val passed: MutableSet<XcfaLocation> = linkedSetOf(),
    val exits: MutableSet<XcfaLocation> = linkedSetOf(),
    var returnsToStart: Boolean = false,
  ) {
    fun absorb(other: Walk) {
      edges += other.edges
      locations += other.locations
      passed += other.passed
      exits += other.exits
      returnsToStart = returnsToStart || other.returnsToStart
    }
  }

  private class Cut(val pieces: List<Block>, val cost: Int, val name: String) {
    val largest = pieces.maxOf { it.edges.size }
  }

  fun best(): List<Block>? {
    if (block.initialLocation !in outgoing) return null
    var best: Cut? = null
    for (cut in listOf(null) + candidates) {
      if (visits > budget) break
      val found = evaluate(cut) ?: continue
      val current = best
      if (
        current == null ||
          compareValuesBy(
            found,
            current,
            { it.cost },
            { it.largest },
            { it.pieces.size },
            { it.name },
          ) < 0
      ) {
        best = found
      }
    }
    return best?.pieces
  }

  private fun evaluate(cut: XcfaLocation?): Cut? {
    val stops = setOfNotNull(cut, exit, entry)
    val starts =
      listOfNotNull(
        block.initialLocation,
        cut,
        exit?.takeIf { it != block.initialLocation && it in outgoing },
      )
    val pieces = mutableListOf<Block>()
    for (start in starts) {
      for (group in groups(start, stops)) {
        if (group.exits.size > 1) return null
        val final = group.exits.singleOrNull() ?: deadEnd(group.locations, start)
        pieces += Block("${block.id}_${pieces.size}", start, final, group.locations, group.edges)
      }
    }
    val owned = pieces.sumOf { it.edges.size }
    if (pieces.size < 2 || owned != reachableEdges.size) return null
    if (pieces.flatMapTo(hashSetOf()) { it.edges } != reachableEdges) return null
    // The successors would lose their predecessor
    if (exit != null && pieces.none { it.finalLocation == exit }) return null
    val cost = cut?.let { c -> reachableEdges.count { it.target == c } } ?: 0
    return Cut(pieces, cost, cut?.name.orEmpty())
  }

  /** The walks from [start]'s edges, merged where they pass through a common location. */
  private fun groups(start: XcfaLocation, stops: Set<XcfaLocation>): List<Walk> {
    val walks = outgoing.getValue(start).map { walk(start, it, stops) }
    val single = walks.any { it.returnsToStart } || (start == block.initialLocation && block.isRoot)
    if (single) return listOf(Walk().apply { walks.forEach(::absorb) })
    val groups = mutableListOf<Walk>()
    for (walk in walks) {
      val overlapping = groups.filter { group -> group.passed.any { it in walk.passed } }
      groups.removeAll(overlapping)
      groups +=
        Walk().apply {
          overlapping.forEach(::absorb)
          absorb(walk)
        }
    }
    return groups
  }

  private fun walk(start: XcfaLocation, first: XcfaEdge, stops: Set<XcfaLocation>): Walk {
    val walk = Walk(locations = linkedSetOf(start))
    val waitlist = ArrayDeque(listOf(first))
    while (waitlist.isNotEmpty()) {
      val edge = waitlist.removeFirst()
      visits++
      if (!walk.edges.add(edge)) continue
      val target = edge.target
      walk.locations += target
      when {
        target in stops -> walk.exits += target
        target == start -> walk.returnsToStart = true
        // Pieces may share a dead end: it has no edges to take
        target !in outgoing -> {}
        walk.passed.add(target) -> waitlist.addAll(outgoing.getValue(target))
      }
    }
    return walk
  }

  private fun deadEnd(locations: Set<XcfaLocation>, start: XcfaLocation): XcfaLocation =
    locations
      .filter { it != start && it !in outgoing }
      .minWithOrNull(compareBy({ it.error }, { it.name }))
      ?: locations.firstOrNull { it != start }
      ?: start
}
