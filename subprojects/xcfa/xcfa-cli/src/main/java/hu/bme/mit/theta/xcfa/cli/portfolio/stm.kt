/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.cli.portfolio

abstract class Node {
    val outEdges: MutableSet<Edge> = LinkedHashSet()
    var parent: STM? = null

    abstract fun execute(): Pair<Any, Any>
}

data class HierarchicalNode(val innerSTM: STM): Node() {
    override fun execute(): Pair<Any, Any> = innerSTM.execute()
}

data class ConfigNode(val config: (inProcess:Boolean) -> Any, val inProcess: Boolean) : Node() {
    override fun execute(): Pair<Any, Any> =
            Pair(config, config(inProcess))
}

data class Edge(val source: Node, val target: Node, val trigger: (Exception) -> Boolean, val guard: (Node, Edge)->Boolean) {
    init {
        source.outEdges.add(this)
    }
}

data class STM(val initNode: Node, val edges: Set<Edge>) {
    init{
        val nodes = edges.map { listOf(it.source, it.target) }.flatten().toSet()
        nodes.forEach {
            check(it.parent == null || it.parent === this) {"Edges not to behave encapsulated (offender: $it)"}
            it.parent = this
        }
    }

    fun execute(): Pair<Any, Any> {
        var currentNode: Node = initNode
        while(true) {
            try {
                return currentNode.execute()
            } catch (e: Exception) {
                val edge: Edge? = currentNode.outEdges.find { it.trigger(e) }
                if (edge != null) {
                    currentNode = edge.target
                } else {
                    throw e
                }
            }
        }
    }
}