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

/** CPAchecker's `BlockGraph`, with exactly one root. */
class BlockGraph(val blocks: Set<Block>) {

  private val blocksById: Map<String, Block> = blocks.associateBy { it.id }

  val root: Block =
    blocks.singleOrNull { it.isRoot }
      ?: error(
        "BlockGraph must have exactly one root block (no predecessors), " +
          "but found ${blocks.count { it.isRoot }} among ${blocks.map(Block::id)}."
      )

  fun successorsOf(block: Block): Set<Block> = block.successorIds.map(::requireBlock).toSet()

  fun predecessorsOf(block: Block): Set<Block> = block.predecessorIds.map(::requireBlock).toSet()

  private fun requireBlock(id: String): Block =
    blocksById[id] ?: error("BlockGraph is inconsistent: no block with id '$id'.")

  fun checkConsistency() {
    for (block in blocks) {
      check(block.initialLocation in block.locations) {
        "Block ${block.id} does not contain its own initial location."
      }
      check(block.finalLocation in block.locations) {
        "Block ${block.id} does not contain its own final location."
      }
      check(block.violationConditionLocation in block.locations) {
        "Block ${block.id} does not contain its own violation-condition location."
      }
      for (successorId in block.successorIds) {
        val successor = requireBlock(successorId)
        check(block.id in successor.predecessorIds) {
          "Block ${block.id} lists ${successor.id} as a successor, but not vice versa."
        }
      }
      for (predecessorId in block.predecessorIds) {
        val predecessor = requireBlock(predecessorId)
        check(block.id in predecessor.successorIds) {
          "Block ${block.id} lists ${predecessor.id} as a predecessor, but not vice versa."
        }
      }
    }
  }

  companion object {

    /** `Y` succeeds `X` iff `Y` starts where `X` ends. */
    fun fromBlocksWithoutEdges(blocksWithoutEdges: Collection<Block>): BlockGraph {
      val byInitialLocation = blocksWithoutEdges.groupBy { it.initialLocation }
      val byFinalLocation = blocksWithoutEdges.groupBy { it.finalLocation }
      val wired =
        blocksWithoutEdges.map { block ->
          block.copy(
            predecessorIds =
              byFinalLocation[block.initialLocation].orEmpty().map(Block::id).toSet(),
            successorIds = byInitialLocation[block.finalLocation].orEmpty().map(Block::id).toSet(),
          )
        }
      return BlockGraph(wired.toSet())
    }
  }
}
