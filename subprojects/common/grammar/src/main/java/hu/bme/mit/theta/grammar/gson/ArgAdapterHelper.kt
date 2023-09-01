/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.grammar.gson

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.ArgNode

data class ArgAdapterHelper<S : State, A : Action>(
    val initNodes: Map<Int, Triple<S, Boolean, Boolean>>,
    val nodes: Map<Int, ArgNodeAdapter<S>>,
    val edges: Map<Int, ArgEdgeAdapter<A>>,
    val coveringEdges: Map<Int, Int>
) {

    constructor(arg: ARG<S, A>) : this(
        initNodes = arg.initNodes.map { Pair(it.id, Triple(it.state, it.isTarget, it.isExpanded)) }
            .toList().associate { it.first to it.second },
        nodes = arg.nodes.map { Pair(it.id, ArgNodeAdapter(it.isTarget, it.state, it.isExpanded)) }
            .toList().associate { it.first to it.second },
        edges = arg.nodes.filter { it.inEdge.isPresent }
            .map { Pair(it.id, ArgEdgeAdapter(it.inEdge.get().source.id, it.inEdge.get().action)) }
            .toList().associate { it.first to it.second },
        coveringEdges = arg.nodes.filter { it.coveringNode.isPresent }
            .map { Pair(it.id, it.coveringNode.get().id) }.toList()
            .associate { it.first to it.second }
    )

    fun instantiate(partialOrd: PartialOrd<S>): ARG<S, A> {
        val arg = ARG.create<S, A>(partialOrd)
        val lut = HashMap<Int, ArgNode<S, A>>()
        initNodes.forEach {
            lut[it.key] = arg.createInitNode(it.value.first, it.value.second)
                .also { n -> if (it.value.third) n.expanded = true }
        }
        arg.initialized = true
        val waitSet = HashSet<Int>(edges.keys)
        while (waitSet.isNotEmpty()) {
            val entry = waitSet.firstOrNull { lut.keys.contains(checkNotNull(edges[it]).source) }
            check(
                entry != null) { "Unreachable node(s) present: $waitSet\nedges: $edges\nlut: $lut" }
            waitSet.remove(entry)
            val edge = checkNotNull(edges[entry])
            lut[entry] = arg.createSuccNode(lut[edge.source], edge.action, checkNotNull(nodes[entry]).state,
                checkNotNull(nodes[entry]).target)
                .also { n -> if (checkNotNull(nodes[entry]).expanded) n.expanded = true }
        }
        coveringEdges.forEach { checkNotNull(lut[it.key]).cover(lut[it.value]) }
        return arg
    }
}


data class ArgNodeAdapter<S : State>(
    val target: Boolean,
    val state: S,
    val expanded: Boolean
)

data class ArgEdgeAdapter<A : Action>(
    val source: Int,
    val action: A,
) {

}