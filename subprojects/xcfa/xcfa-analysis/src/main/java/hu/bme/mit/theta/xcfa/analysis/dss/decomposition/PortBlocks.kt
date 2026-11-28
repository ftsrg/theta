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

/** Regions collapse into one block, growing until they have a single entry and exit. */
const val NO_PORT_BLOCKS = 0

/** How many port blocks one region may become before it falls back to a single block. */
const val DEFAULT_PORT_BLOCK_LIMIT = 8

internal const val PORT_PREFIX = "MP"

/** One more than the largest `MC<n>`/`MP<n>` index among the blocks, so the two never collide. */
internal fun nextCollapsedIndex(blockGraph: BlockGraph): Int =
  blockGraph.blocks
    .mapNotNull { COLLAPSED_ID.find(it.id)?.groupValues?.get(1)?.toIntOrNull() }
    .maxOrNull()
    ?.plus(1) ?: 0

private val COLLAPSED_ID = Regex("^M[CP](\\d+)")

/**
 * [initialRegion] replaced by its port blocks: one per entry and exit reachable from it, each with
 * the region's edges reachable from its entry, so the paths leaving by other exits end inside it.
 * An entry that reaches no exit gets one block ending at a dead end.
 *
 * The region first grows, at most [maxGrowth] times, until no entry is also an exit (such a block
 * would succeed itself), and the root entry reaches one exit only (the graph has a single root).
 * Null if it cannot, or if it would take more than [limit] blocks.
 */
internal fun collapseToPortBlocks(
  blockGraph: BlockGraph,
  initialRegion: Set<String>,
  idPrefix: String,
  limit: Int,
  maxGrowth: Int = Int.MAX_VALUE,
): BlockGraph? {
  val byId = blockGraph.blocks.associateBy { it.id }
  val region = initialRegion.toMutableSet()
  var growth = 0
  while (true) {
    val members = region.sorted().map(byId::getValue)
    val entering = members.filter { it.isRoot || it.predecessorIds.any { p -> p !in region } }
    val leaving = members.filter { it.successorIds.any { s -> s !in region } }
    val entries = entering.mapTo(linkedSetOf()) { it.initialLocation }
    val exits = leaving.mapTo(linkedSetOf()) { it.finalLocation }
    val shared = entries intersect exits
    val rootEntry = members.singleOrNull { it.isRoot }?.initialLocation
    val ports = if (shared.isEmpty()) portsOf(members, entries, exits) else null
    if (ports != null && ports.count { it.entry == rootEntry } <= 1) {
      if (ports.size > limit) return null
      val blocks =
        ports.mapIndexed { index, (entry, exit, edges) ->
          Block(
            id = "${idPrefix}_$index",
            initialLocation = entry,
            finalLocation = exit,
            locations = edges.flatMapTo(linkedSetOf(entry)) { listOf(it.source, it.target) },
            edges = edges,
          )
        }
      return BlockGraph.fromBlocksWithoutEdges(
        blockGraph.blocks.filter { it.id !in region } + blocks
      )
    }
    if (ports == null && shared.isEmpty()) return null
    if (growth++ >= maxGrowth) return null
    fun outside(ids: Collection<String>) = ids.filterTo(sortedSetOf()) { it !in region }
    val grow =
      if (shared.isNotEmpty()) {
        outside(entering.filter { it.initialLocation in shared }.flatMap { it.predecessorIds })
          .ifEmpty {
            outside(leaving.filter { it.finalLocation in shared }.flatMap { it.successorIds })
          }
      } else {
        // The root entry reaches several exits: grow towards where they join
        outside(leaving.flatMap { it.successorIds })
      }
    if (grow.isEmpty()) return null
    region += grow
  }
}

private data class Port(val entry: XcfaLocation, val exit: XcfaLocation, val edges: Set<XcfaEdge>)

/**
 * Every (entry, exit, edges) port of a region whose entries are no exits, or null if one has none.
 */
private fun portsOf(
  members: List<Block>,
  entries: Set<XcfaLocation>,
  exits: Set<XcfaLocation>,
): List<Port>? {
  val bySource = members.flatMapTo(linkedSetOf()) { it.edges }.groupBy { it.source }
  return entries.flatMap { entry ->
    val edges = linkedSetOf<XcfaEdge>()
    val reached = linkedSetOf(entry)
    val waitlist = ArrayDeque(listOf(entry))
    while (waitlist.isNotEmpty()) {
      for (edge in bySource[waitlist.removeFirst()].orEmpty()) {
        edges += edge
        if (reached.add(edge.target)) waitlist.addLast(edge.target)
      }
    }
    val finals =
      exits.filter { it in reached }.ifEmpty { listOfNotNull(deadEnd(reached - entries)) }
    if (finals.isEmpty()) return null
    finals.map { Port(entry, it, edges) }
  }
}

/** Not an entry: a block ending there would be followed by the ones starting there. */
private fun deadEnd(candidates: Set<XcfaLocation>): XcfaLocation? {
  val sorted = candidates.sortedBy { it.name }
  return sorted.filter { it.outgoingEdges.isEmpty() }.minByOrNull { it.error }
    ?: sorted.firstOrNull()
}
