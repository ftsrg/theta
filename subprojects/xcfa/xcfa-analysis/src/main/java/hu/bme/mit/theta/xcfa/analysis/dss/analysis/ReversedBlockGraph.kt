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
package hu.bme.mit.theta.xcfa.analysis.dss.analysis

import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation

/**
 * The blocks of [forward] reversed, so the two directions share their block boundaries, where their
 * conditions can meet. A reversed block containing an error location is cut linearly.
 */
fun reverseBlockGraph(forward: BlockGraph, reversal: ProgramReversal): BlockGraph {
  val boundaries =
    forward.blocks
      .flatMap { listOf(it.initialLocation, it.finalLocation) }
      .mapNotNullTo(linkedSetOf()) { reversal.reversedOf[it] }
  return runCatching { reverseBlocks(forward, reversal, boundaries) }.getOrNull()
    ?: LinearBlockDecomposition {
        LinearBlockDecomposition.defaultIsBlockEnd(it) || it in boundaries
      }
      .decompose(reversal.procedure)
      .also { it.checkConsistency() }
}

private fun reverseBlocks(
  forward: BlockGraph,
  reversal: ProgramReversal,
  boundaries: Set<XcfaLocation>,
): BlockGraph {
  val procedure = reversal.procedure
  val reversedEdgeOf =
    reversal.originalEdgeOf.entries.associate { (reversed, it) -> it to reversed }
  val blocks = mutableListOf<Block>()
  fun edgeBlock(id: String, edge: XcfaEdge) =
    Block(id, edge.source, edge.target, setOf(edge.source, edge.target), setOf(edge))

  val init = procedure.initLoc
  val toHub = init.outgoingEdges.single()
  blocks += edgeBlock("init", toHub)
  toHub.target.outgoingEdges.forEachIndexed { i, edge -> blocks += edgeBlock("error$i", edge) }
  // Only `__rev_err` is not a clone, and its edge belongs to no forward block
  procedure.errorLoc
    .filter { it !in reversal.originalOf }
    .ifPresent { blocks += edgeBlock("entry", it.incomingEdges.single()) }

  for (block in forward.blocks.sortedBy { it.id }) {
    val edges = block.edges.mapNotNullTo(linkedSetOf()) { reversedEdgeOf[it] }
    if (edges.isEmpty()) continue
    val entry = reversal.reversedOf[block.finalLocation]
    val exit = reversal.reversedOf[block.initialLocation]
    val locations = edges.flatMapTo(linkedSetOf()) { listOf(it.source, it.target) }
    val candidate =
      if (entry != null && exit != null) Block(block.id, entry, exit, locations, edges) else null
    val whole = candidate?.takeIf(::isClosed)
    if (whole != null) blocks += whole else blocks += cutLinearly(block.id, edges, boundaries)
  }

  val graph = BlockGraph.fromBlocksWithoutEdges(blocks)
  graph.checkConsistency()
  val covered = graph.blocks.flatMap { it.edges }
  check(covered.size == covered.toSet().size && covered.toSet() == procedure.edges) {
    "The reversed blocks do not partition the reversed program"
  }
  return graph
}

/** One entry, one exit: every other location keeps all its edges inside, and is reachable. */
private fun isClosed(block: Block): Boolean {
  val inner = block.locations - block.initialLocation - block.finalLocation
  val closed =
    inner.all { location ->
      location.incomingEdges.all { it in block.edges } &&
        location.outgoingEdges.all { it in block.edges }
    }
  val reached = linkedSetOf(block.initialLocation)
  val pending = ArrayDeque(listOf(block.initialLocation))
  while (pending.isNotEmpty()) {
    for (edge in pending.removeFirst().outgoingEdges) {
      if (edge in block.edges && reached.add(edge.target)) pending.addLast(edge.target)
    }
  }
  return closed && reached == block.locations
}

/** Chains of [edges] between boundaries, as the linear decomposition cuts them. */
private fun cutLinearly(
  id: String,
  edges: Set<XcfaEdge>,
  boundaries: Set<XcfaLocation>,
): List<Block> {
  fun isEnd(location: XcfaLocation) =
    location in boundaries || LinearBlockDecomposition.defaultIsBlockEnd(location)
  val starts =
    edges.map { it.source }.filter { isEnd(it) || it.incomingEdges.none { e -> e in edges } }
  return starts.distinct().flatMap { start ->
    start.outgoingEdges
      .filter { it in edges }
      .mapIndexed { i, first ->
        val chain = linkedSetOf(first)
        var location = first.target
        while (!isEnd(location)) {
          val next = location.outgoingEdges.single()
          check(next in edges && chain.add(next)) { "Block $id cannot be cut linearly" }
          location = next.target
        }
        val locations = chain.flatMapTo(linkedSetOf()) { listOf(it.source, it.target) }
        Block("$id.${start.name}.$i", start, location, locations, chain)
      }
  }
}
