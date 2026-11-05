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

const val NO_MERGE_LIMIT = -1

/** `MH<n>` (horizontal) and `MV<n>` (vertical) ids, counting across passes. */
class MergeIdGenerator(private var horizontal: Int = 0, private var vertical: Int = 0) {

  fun nextHorizontal(): String = "MH${horizontal++}"

  fun nextVertical(): String = "MV${vertical++}"

  companion object {

    fun startingAfter(blockGraph: BlockGraph): MergeIdGenerator {
      fun next(prefix: String) =
        blockGraph.blocks
          .filter { it.id.startsWith(prefix) }
          .mapNotNull { it.id.removePrefix(prefix).toIntOrNull() }
          .maxOrNull()
          ?.plus(1) ?: 0
      return MergeIdGenerator(next("MH"), next("MV"))
    }
  }
}

private fun Collection<Block>.sortedById(): List<Block> = sortedBy { it.id }

/** CPAchecker's `mergeHorizontally`. */
fun horizontalMergePass(
  blockGraph: BlockGraph,
  targetBlockCount: Int = 0,
  largestHorizontalMerge: Int = NO_MERGE_LIMIT,
  ids: MergeIdGenerator = MergeIdGenerator.startingAfter(blockGraph),
): BlockGraph {
  val groups =
    LinkedHashMap<Triple<Set<String>, Set<String>, Any>, MutableList<Block>>().apply {
      for (block in blockGraph.blocks.sortedById()) {
        getOrPut(Triple(block.predecessorIds, block.successorIds, block.finalLocation)) {
            mutableListOf()
          }
          .add(block)
      }
    }

  val idRemap = mutableMapOf<String, String>()
  var blockCount = blockGraph.blocks.size
  for ((scope, group) in groups.entries.toList()) {
    if (blockCount <= targetBlockCount) break
    if (group.size <= 1) continue
    val largeBlocks = group.count { it.locations.size > largestHorizontalMerge }
    if (largestHorizontalMerge >= 0 && largeBlocks > 1) continue

    val merged = mergeHorizontally(group, ids.nextHorizontal())
    for (member in group) {
      idRemap[member.id] = merged.id
    }
    groups[scope] = mutableListOf(merged)
    blockCount -= group.size - 1
  }

  if (idRemap.isEmpty()) {
    return blockGraph
  }
  return BlockGraph(groups.values.flatten().map { remapBlockIds(it, idRemap) }.toSet())
}

private fun mergeHorizontally(group: List<Block>, id: String): Block {
  val first = group.first()
  return Block(
    id = id,
    initialLocation = first.initialLocation,
    finalLocation = first.finalLocation,
    locations = group.flatMapTo(mutableSetOf()) { it.locations },
    edges = group.flatMapTo(mutableSetOf()) { it.edges },
    predecessorIds = first.predecessorIds,
    successorIds = first.successorIds,
  )
}

/** CPAchecker's `mergeVertically`. */
fun verticalMergePass(
  blockGraph: BlockGraph,
  targetBlockCount: Int = 0,
  ids: MergeIdGenerator = MergeIdGenerator.startingAfter(blockGraph),
): BlockGraph {
  val blocks = LinkedHashMap<String, Block>()
  blockGraph.blocks.sortedById().forEach { blocks[it.id] = it }
  val idRemap = mutableMapOf<String, String>()
  fun resolve(id: String): String {
    var current = id
    while (true) current = idRemap[current] ?: return current
  }

  val removed = mutableSetOf<String>()
  for (x in blockGraph.blocks.sortedById()) {
    if (x.id in removed) continue
    val successorId = x.successorIds.singleOrNull()?.let(::resolve) ?: continue
    if (successorId == x.id) continue
    val y = blocks[successorId] ?: continue
    if (y.predecessorIds.size != 1) continue

    val merged =
      Block(
        id = ids.nextVertical(),
        initialLocation = x.initialLocation,
        finalLocation = y.finalLocation,
        locations = x.locations + y.locations,
        edges = x.edges + y.edges,
        predecessorIds = x.predecessorIds,
        successorIds = y.successorIds,
      )
    blocks.remove(x.id)
    blocks.remove(y.id)
    blocks[merged.id] = merged
    removed += x.id
    removed += y.id
    idRemap[x.id] = merged.id
    idRemap[y.id] = merged.id
    if (blocks.size <= targetBlockCount) break
  }

  if (idRemap.isEmpty()) {
    return blockGraph
  }
  return BlockGraph(
    blocks.values
      .map { block ->
        block.copy(
          predecessorIds = block.predecessorIds.map(::resolve).toSet(),
          successorIds = block.successorIds.map(::resolve).toSet(),
        )
      }
      .toSet()
  )
}

fun horizontalMerge(
  blockGraph: BlockGraph,
  targetBlockCount: Int = 1,
  largestHorizontalMerge: Int = NO_MERGE_LIMIT,
  ids: MergeIdGenerator = MergeIdGenerator.startingAfter(blockGraph),
): BlockGraph =
  repeatUntilStable(blockGraph, targetBlockCount) {
    horizontalMergePass(it, targetBlockCount, largestHorizontalMerge, ids)
  }

fun verticalMerge(
  blockGraph: BlockGraph,
  targetBlockCount: Int = 1,
  ids: MergeIdGenerator = MergeIdGenerator.startingAfter(blockGraph),
): BlockGraph =
  repeatUntilStable(blockGraph, targetBlockCount) { verticalMergePass(it, targetBlockCount, ids) }

private fun repeatUntilStable(
  blockGraph: BlockGraph,
  targetBlockCount: Int,
  pass: (BlockGraph) -> BlockGraph,
): BlockGraph {
  var current = blockGraph
  while (current.blocks.size > targetBlockCount) {
    val next = pass(current)
    if (next.blocks.size == current.blocks.size) return next
    current = next
  }
  return current
}

private fun remapBlockIds(block: Block, idRemap: Map<String, String>): Block =
  block.copy(
    predecessorIds = block.predecessorIds.map { idRemap[it] ?: it }.toSet(),
    successorIds = block.successorIds.map { idRemap[it] ?: it }.toSet(),
  )

/** CPAchecker's `MergeBlockNodesDecomposition`. */
fun mergeToTargetBlockCount(
  blockGraph: BlockGraph,
  targetBlockCount: Int,
  largestHorizontalMerge: Int = NO_MERGE_LIMIT,
): BlockGraph {
  val ids = MergeIdGenerator.startingAfter(blockGraph)
  var current = blockGraph
  while (current.blocks.size > targetBlockCount) {
    val sizeBefore = current.blocks.size
    current = horizontalMergePass(current, targetBlockCount, largestHorizontalMerge, ids)
    if (current.blocks.size <= targetBlockCount) break
    current = verticalMergePass(current, targetBlockCount, ids)
    if (current.blocks.size == sizeBefore) break
  }
  return current
}
