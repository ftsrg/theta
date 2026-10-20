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

const val DEFAULT_CUT_BLOCK_COUNT = 2

/** Edge visits of the search, about a few seconds. */
const val DEFAULT_CUT_SEARCH_BUDGET = 200_000_000L

enum class CutLoopHandling(val decompositionName: String) {
  ALLOW("MIN_CUT"),
  ABSORB_SELF_LOOPS("MIN_CUT_ABSORB_SELF_LOOPS"),
  FORBID("MIN_CUT_ACYCLIC"),
}

/** A cut with the fewest edges between blocks, then the most equal block sizes. */
class MinCutDecomposition(
  private val blockCount: Int = DEFAULT_CUT_BLOCK_COUNT,
  private val loopHandling: CutLoopHandling = CutLoopHandling.ALLOW,
  private val searchBudget: Long = DEFAULT_CUT_SEARCH_BUDGET,
) : DssBlockDecomposition {

  init {
    require(blockCount >= 1) { "The cut block count must be positive, got $blockCount" }
  }

  override fun decompose(procedure: XcfaProcedure): BlockGraph = cut(procedure).blockGraph

  fun cut(procedure: XcfaProcedure): MinCut {
    if (loopHandling == CutLoopHandling.ALLOW) return plainCut(procedure)
    val reason =
      try {
        loopHandledCut(procedure)?.let {
          return it
        } ?: notPossibleReason(procedure)
      } catch (e: InterruptedException) {
        throw e
      } catch (e: Exception) {
        "${e.javaClass.simpleName}: ${e.message}"
      }
    return plainCut(procedure)
      .withFallback("${loopHandling.decompositionName} not possible ($reason)")
  }

  private fun plainCut(procedure: XcfaProcedure): MinCut {
    val search = CutSearch(procedure, acyclicOnly = false, searchBudget)
    for (count in blockCount downTo 2) {
      val found = search.best(count - 1) ?: continue
      return MinCut(found, blockCount, found.graph, search.exhaustive)
    }
    return MinCut(
      null,
      blockCount,
      SingleBlockDecomposition.decompose(procedure),
      search.exhaustive,
    )
  }

  private fun loopHandledCut(procedure: XcfaProcedure): MinCut? {
    val acyclicOnly = loopHandling == CutLoopHandling.FORBID
    val search = CutSearch(procedure, acyclicOnly, searchBudget)
    for (count in blockCount downTo 2) {
      val found = search.best(count - 1) ?: continue
      if (acyclicOnly) return MinCut(found, blockCount, found.graph, search.exhaustive)
      val collapsed = collapseCycles(found.graph, onlySelfLoops = true)
      return if (collapsed.blocks.size < 2) null
      else MinCut(found, blockCount, collapsed, search.exhaustive)
    }
    return null
  }

  private fun notPossibleReason(procedure: XcfaProcedure): String =
    when (loopHandling) {
      CutLoopHandling.FORBID ->
        "no cut of ${procedure.name} into 2..$blockCount blocks has an acyclic block graph"
      else -> "no cut of ${procedure.name} into 2..$blockCount blocks keeps two blocks"
    }
}

class MinCut
internal constructor(
  private val candidate: CutCandidate?,
  val requestedBlockCount: Int,
  val blockGraph: BlockGraph,
  val exhaustive: Boolean,
  val fallbackReason: String? = null,
) {

  internal fun withFallback(reason: String) =
    MinCut(candidate, requestedBlockCount, blockGraph, exhaustive, reason)

  val cutLocations: List<XcfaLocation> = candidate?.cutLocations.orEmpty()
  val cutEdges: List<XcfaEdge> = candidate?.cutEdges.orEmpty()
  val cutBlocks: List<Block> = candidate?.blocks.orEmpty()

  fun describe(): List<String> = buildList {
    val collapsed =
      if (blockGraph.blocks.size != cutBlocks.size.coerceAtLeast(1))
        ", ${blockGraph.blocks.size} blocks after collapsing self loops"
      else ""
    val fallback = fallbackReason?.let { ", fell back to MIN_CUT: $it" }.orEmpty()
    add(
      "DSS min cut: ${cutBlocks.size.coerceAtLeast(1)} blocks (requested $requestedBlockCount), " +
        "${cutEdges.size} cut edges at ${cutLocations.map { it.name }}, " +
        "search ${if (exhaustive) "exhaustive" else "stopped at the budget"}$collapsed$fallback"
    )
    cutEdges.forEach {
      add("DSS min cut edge: ${it.source.name} -> ${it.target.name} (${it.label})")
    }
    cutBlocks.forEachIndexed { index, block ->
      val side =
        when {
          cutBlocks.size != 2 -> ""
          index == 0 -> " (before the cut)"
          else -> " (after the cut)"
        }
      val names = block.locations.map { it.name }.sorted()
      val shown =
        if (names.size <= MAX_LOGGED_LOCATIONS) names.toString()
        else
          names.take(MAX_LOGGED_LOCATIONS).toString() +
            " ... ${names.size - MAX_LOGGED_LOCATIONS} more"
      add(
        "DSS min cut block ${block.id}$side: ${block.initialLocation.name} -> " +
          "${block.finalLocation.name}, ${block.locations.size} locations $shown"
      )
    }
  }

  private companion object {
    const val MAX_LOGGED_LOCATIONS = 40
  }
}

internal class CutCandidate(
  val cutLocations: List<XcfaLocation>,
  val cutEdges: List<XcfaEdge>,
  val blocks: List<Block>,
  val graph: BlockGraph,
  val spread: Int,
  val deviation: Int,
)

private class CutSearch(
  private val procedure: XcfaProcedure,
  private val acyclicOnly: Boolean,
  private val budget: Long,
) {

  private val reachableEdges: Set<XcfaEdge> = buildSet {
    val seen = mutableSetOf(procedure.initLoc)
    val waitlist = ArrayDeque(listOf(procedure.initLoc))
    while (waitlist.isNotEmpty()) {
      for (edge in waitlist.removeFirst().outgoingEdges) {
        add(edge)
        if (seen.add(edge.target)) waitlist.addLast(edge.target)
      }
    }
  }

  private fun inDegree(location: XcfaLocation) =
    location.incomingEdges.count { it in reachableEdges }

  private val candidates: List<XcfaLocation> =
    reachableEdges
      .map { it.target }
      .distinct()
      .filter { it != procedure.initLoc && it.outgoingEdges.isNotEmpty() }
      .sortedWith(compareBy({ inDegree(it) }, { it.name }))

  private val costs = candidates.map(::inDegree)
  private var visits = 0L
  var exhaustive = true
    private set

  fun best(cuts: Int): CutCandidate? {
    if (cuts > candidates.size) return null
    var best: CutCandidate? = null
    var bestCost = Int.MAX_VALUE
    val chosen = ArrayList<Int>(cuts)

    fun search(from: Int, cost: Int) {
      if (chosen.size == cuts) {
        if (cost > bestCost) return
        val candidate = evaluate(chosen.map(candidates::get)) ?: return
        if (best == null || cost < bestCost || isBetterBalanced(candidate, best!!)) {
          best = candidate
          bestCost = cost
        }
        return
      }
      val needed = cuts - chosen.size
      for (index in from..candidates.size - needed) {
        // candidates are sorted by cost, so the rest cost at least as much as this one
        if (cost + costs[index] * needed > bestCost) break
        if (visits > budget) {
          exhaustive = false
          return
        }
        chosen.add(index)
        search(index + 1, cost + costs[index])
        chosen.removeAt(chosen.size - 1)
      }
    }

    search(0, 0)
    return best
  }

  private fun isBetterBalanced(a: CutCandidate, b: CutCandidate): Boolean =
    compareValuesBy(a, b, { it.spread }, { it.deviation }) < 0

  private fun evaluate(cutLocations: List<XcfaLocation>): CutCandidate? {
    val cutSet = cutLocations.toSet()
    val owner = HashMap<XcfaEdge, Int>()
    val blocks = ArrayList<Block>()
    for ((index, start) in (listOf(procedure.initLoc) + cutLocations).withIndex()) {
      val locations = linkedSetOf(start)
      val edges = linkedSetOf<XcfaEdge>()
      val exits = linkedSetOf<XcfaLocation>()
      val waitlist = ArrayDeque(listOf(start))
      val expanded = mutableSetOf(start)
      while (waitlist.isNotEmpty()) {
        for (edge in waitlist.removeFirst().outgoingEdges) {
          visits++
          if (owner.putIfAbsent(edge, index) != null) return null
          edges += edge
          val target = edge.target
          locations += target
          if (target in cutSet) exits += target
          else if (expanded.add(target)) waitlist.addLast(target)
        }
      }
      if (exits.size > 1) return null
      val final =
        exits.singleOrNull()
          ?: locations
            .filter { it.outgoingEdges.isEmpty() }
            .minWithOrNull(compareBy({ it.error }, { it.name }))
          ?: locations.firstOrNull { it != start }
          ?: start
      blocks += Block("K$index", start, final, locations, edges)
    }
    val graph = BlockGraph.fromBlocksWithoutEdges(blocks)
    if (acyclicOnly && graph.getStatistics().cyclicSccs > 0) return null
    val wired = blocks.map { block -> graph.blocks.single { it.id == block.id } }
    val sizes = wired.map { it.locations.size }
    return CutCandidate(
      cutLocations,
      reachableEdges
        .filter { it.target in cutSet }
        .sortedBy { "${it.source.name}->${it.target.name}" },
      wired,
      graph,
      spread = sizes.max() - sizes.min(),
      deviation = sizes.sumOf { kotlin.math.abs(it * sizes.size - sizes.sum()) },
    )
  }
}
