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
 * A block's locations and edges copied. A loop head that is both entry and exit gets an [entry]
 * copy of its own (CPAchecker's INITIAL vs. FINAL), so one traversal covers one iteration.
 */
class BlockClone(
  /** Every location of the block, to its copy; the entry copy of a loop head is not in here. */
  val locations: Map<XcfaLocation, XcfaLocation>,
  val entry: XcfaLocation,
  val exit: XcfaLocation,
  val edges: Set<XcfaEdge>,
  /** Each copy, including the entry copy, to the location of the block it copies. */
  val originalLocations: Map<XcfaLocation, XcfaLocation>,
  /** Each copied edge, to the edge of the block it copies. */
  val originalEdges: Map<XcfaEdge, XcfaEdge>,
)

/**
 * [block] copied, with only [edges] of it (all by default); the copies of its error locations are
 * error locations only if [keepErrors].
 */
fun cloneBlock(
  block: Block,
  keepErrors: Boolean = true,
  edges: Collection<XcfaEdge> = block.edges,
): BlockClone {
  fun copyOf(original: XcfaLocation, nameSuffix: String = "") =
    XcfaLocation(
      original.name + nameSuffix,
      original.initial,
      original.final,
      original.error && keepErrors,
      original.metadata,
    )

  val copies: Map<XcfaLocation, XcfaLocation> = block.locations.associateWith { copyOf(it) }
  val splitEntry = block.initialLocation == block.finalLocation
  val entry =
    if (splitEntry) copyOf(block.initialLocation, "__entry")
    else copies.getValue(block.initialLocation)

  val copiedEdges = linkedSetOf<XcfaEdge>()
  val originalEdges = mutableMapOf<XcfaEdge, XcfaEdge>()
  for (original in edges) {
    val source =
      if (splitEntry && original.source == block.initialLocation) entry
      else copies.getValue(original.source)
    val target = copies.getValue(original.target)
    val copy = XcfaEdge(source, target, original.label, original.metadata)
    source.outgoingEdges.add(copy)
    target.incomingEdges.add(copy)
    copiedEdges.add(copy)
    originalEdges[copy] = original
  }
  return BlockClone(
    copies,
    entry,
    copies.getValue(block.finalLocation),
    copiedEdges,
    copies.entries.associate { (original, copy) -> copy to original } +
      (entry to block.initialLocation),
    originalEdges,
  )
}
