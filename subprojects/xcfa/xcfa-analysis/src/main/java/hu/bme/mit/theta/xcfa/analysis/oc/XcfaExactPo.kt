/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

private data class GlobalEdge(
  val pid: Int,
  val source: XcfaLocation?,
  val target: XcfaLocation,
  val label: XcfaLabel?,
) {

  constructor(pid: Int, edge: XcfaEdge) : this(pid, edge.source, edge.target, edge.label)

  constructor(event: E) : this(event.pid, event.edge)
}

private data class LocalEdge(
  val source: XcfaLocation?,
  val target: XcfaLocation,
  val label: XcfaLabel?,
) {
  constructor(edge: XcfaEdge) : this(edge.source, edge.target, edge.label)

  constructor(edge: GlobalEdge) : this(edge.source, edge.target, edge.label)
}

internal class XcfaExactPo(private val threads: Set<Thread>) {

  private val reachableEdges = threads.associate { it.pid to ReachableEdges(it.procedure) }

  /**
   * Global PO check. If from and to belong to the same atomic block, true is returned; this case
   * has to be handled on the caller side.
   */
  fun isPo(from: E?, to: E): Boolean {
    from ?: return true
    if (from.clkId == to.clkId) return true
    val possiblePathPoints = mutableListOf(GlobalEdge(from))
    val visited = mutableSetOf<GlobalEdge>()
    while (possiblePathPoints.isNotEmpty()) {
      val current = possiblePathPoints.removeFirst()
      if (!visited.add(current)) continue
      if (current.pid == to.pid && reachableEdges[current.pid]!!.reachable(current, to.edge))
        return true

      threads
        .filter {
          it.startEvent?.pid == current.pid &&
            reachableEdges[current.pid]!!.reachable(current, it.startEvent.edge)
        }
        .forEach { thread ->
          possiblePathPoints.add(GlobalEdge(thread.pid, null, thread.procedure.initLoc, null))
        }

      threads
        .find { it.pid == current.pid }
        ?.let { thread ->
          thread.joinEvents.forEach { possiblePathPoints.add(GlobalEdge(it.pid, it.edge)) }
        }
    }

    return false
  }
}

private class ReachableEdges(procedure: XcfaProcedure) {

  private infix fun XcfaLocation?.to(other: XcfaLocation) = LocalEdge(this, other, null)

  private val ids = mutableMapOf<LocalEdge, Int>()
  private var reachable: Array<Array<Boolean>>

  init {
    val toVisit = mutableListOf(null to procedure.initLoc)
    val initials = mutableListOf<Pair<Int, Int>>()
    while (toVisit.isNotEmpty()) { // assumes xcfa contains no cycles (an OC checker requirement)
      val edge = toVisit.removeFirst()
      val id = ids.size
      ids[edge] = id

      if (edge.source == procedure.initLoc) {
        initials.add(ids[null to procedure.initLoc]!! to id)
      } else {
        edge.source
          ?.incomingEdges
          ?.filter { LocalEdge(it) in ids }
          ?.forEach { initials.add(ids[LocalEdge(it)]!! to id) }
      }
      edge.target.outgoingEdges
        .filter { LocalEdge(it) in ids }
        .forEach { initials.add(id to ids[LocalEdge(it)]!!) }

      val toAdd =
        edge.target.outgoingEdges.map { LocalEdge(it) }.filter { it !in ids && it !in toVisit }
      toVisit.addAll(toAdd)
    }
    reachable = Array(ids.size) { Array(ids.size) { false } }
    close(initials) // close reachable transitively
  }

  fun reachable(from: GlobalEdge, to: XcfaEdge): Boolean =
    reachable[ids[LocalEdge(from)]!!][ids[LocalEdge(to)]!!]

  private fun close(initials: List<Pair<Int, Int>>) {
    val toClose = initials.toMutableList()
    while (toClose.isNotEmpty()) {
      val (from, to) = toClose.removeFirst()
      if (reachable[from][to]) continue

      reachable[from][to] = true
      reachable[to].forEachIndexed { i, b -> if (b && !reachable[from][i]) toClose.add(from to i) }
      reachable.forEachIndexed { i, b -> if (b[from] && !reachable[i][to]) toClose.add(i to to) }
    }
    for (i in reachable.indices) reachable[i][i] = true
  }
}
