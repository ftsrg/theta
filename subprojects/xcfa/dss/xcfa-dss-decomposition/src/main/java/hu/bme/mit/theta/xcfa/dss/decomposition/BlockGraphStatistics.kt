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

/**
 * Shape of a [BlockGraph]'s block connections (`--dss-block-graph-stats-only`). [edges] counts
 * block pairs incl. self loops; [cyclicSccs] counts SCCs with a cycle; [largestScc] is in blocks.
 */
data class BlockGraphStatistics(
  val blocks: Int,
  val edges: Int,
  val selfLoops: Int,
  val backAndForthPairs: Int,
  val cyclicSccs: Int,
  val largestScc: Int,
  val maxOutDegree: Int,
  val maxInDegree: Int,
  val maxBlockLocations: Int,
) {

  override fun toString(): String =
    "blocks=$blocks edges=$edges selfLoops=$selfLoops backAndForth=$backAndForthPairs " +
      "cyclicSccs=$cyclicSccs largestScc=$largestScc maxOut=$maxOutDegree maxIn=$maxInDegree " +
      "maxBlockLocations=$maxBlockLocations"
}

fun BlockGraph.statistics(): BlockGraphStatistics {
  val successors = blocks.associate { it.id to it.successorIds }
  val sccs = stronglyConnectedComponents(successors)
  return BlockGraphStatistics(
    blocks = blocks.size,
    edges = blocks.sumOf { it.successorIds.size },
    selfLoops = blocks.count { it.id in it.successorIds },
    backAndForthPairs =
      blocks.sumOf { a -> a.successorIds.count { b -> b > a.id && a.id in successors[b]!! } },
    cyclicSccs = sccs.count { scc -> scc.size > 1 || scc.single().let { it in successors[it]!! } },
    largestScc = sccs.maxOfOrNull { it.size } ?: 0,
    maxOutDegree = blocks.maxOfOrNull { it.successorIds.size } ?: 0,
    maxInDegree = blocks.maxOfOrNull { it.predecessorIds.size } ?: 0,
    maxBlockLocations = blocks.maxOfOrNull { it.locations.size } ?: 0,
  )
}

/** Tarjan's algorithm, iterative so that long block chains cannot overflow the stack. */
internal fun stronglyConnectedComponents(successors: Map<String, Set<String>>): List<Set<String>> {
  val index = mutableMapOf<String, Int>()
  val lowLink = mutableMapOf<String, Int>()
  val onStack = mutableSetOf<String>()
  val stack = ArrayDeque<String>()
  val components = mutableListOf<Set<String>>()
  for (start in successors.keys) {
    if (start in index) continue
    val work = ArrayDeque<Pair<String, Iterator<String>>>()
    fun visit(node: String) {
      index[node] = index.size
      lowLink[node] = index[node]!!
      stack.addLast(node)
      onStack += node
      work.addLast(node to successors[node]!!.iterator())
    }
    visit(start)
    while (work.isNotEmpty()) {
      val (node, children) = work.last()
      if (children.hasNext()) {
        val child = children.next()
        if (child !in index) visit(child)
        else if (child in onStack) lowLink[node] = minOf(lowLink[node]!!, index[child]!!)
        continue
      }
      work.removeLast()
      work.lastOrNull()?.let { (parent, _) ->
        lowLink[parent] = minOf(lowLink[parent]!!, lowLink[node]!!)
      }
      if (lowLink[node] == index[node]) {
        val component = mutableSetOf<String>()
        do {
          val member = stack.removeLast()
          onStack -= member
          component += member
        } while (member != node)
        components += component
      }
    }
  }
  return components
}
