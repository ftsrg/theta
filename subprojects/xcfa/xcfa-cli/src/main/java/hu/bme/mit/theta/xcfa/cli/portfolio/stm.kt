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

package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.xcfa.cli.XcfaCegarConfig

abstract class Node(val name: String) {

    val outEdges: MutableSet<Edge> = LinkedHashSet()
    var parent: STM? = null

    abstract fun execute(): Pair<Any, Any>
    abstract fun visualize(): String
}

class HierarchicalNode(name: String, private val innerSTM: STM) : Node(name) {

    override fun execute(): Pair<Any, Any> = innerSTM.execute()
    override fun visualize(): String = """state $name {
${innerSTM.visualize()}
}""".trimIndent()
}

class ConfigNode(name: String, private val config: XcfaCegarConfig,
    private val check: (inProcess: Boolean, config: XcfaCegarConfig) -> SafetyResult<*, *>,
    private val inProcess: Boolean) : Node(name) {

    override fun execute(): Pair<Any, Any> {
        println("Current configuration: $config (inProcess=$inProcess)")
        return Pair(config, check(inProcess, config))
    }

    override fun visualize(): String = config.visualize(inProcess).lines()
        .map { "state $name: $it" }.reduce { a, b -> "$a\n$b" }
}

data class Edge(val source: Node,
    val target: Node,
    val trigger: (Exception) -> Boolean,
    val guard: (Node, Edge) -> Boolean = { _, _ -> true }) {

    init {
        source.outEdges.add(this)
    }

    fun visualize(): String = """${source.name} --> ${target.name} : $trigger """

}

// if the exceptions set is empty, it catches all exceptions
class ExceptionTrigger(
    val exceptions: Set<Exception> = emptySet(),
    val fallthroughExceptions: Set<Exception> = emptySet(),
    val label: String? = null
) : (Exception) -> Boolean {

    constructor(vararg exceptions: Exception, label: String? = null) : this(exceptions.toSet(),
        label = label)

    override fun invoke(e: Exception): Boolean =
        if (exceptions.isNotEmpty())
            exceptions.contains(e) && !fallthroughExceptions.contains(e)
        else
            !fallthroughExceptions.contains(e)

    override fun toString(): String =
        label ?: ((if (exceptions.isNotEmpty()) exceptions.toString() else "*") +
            (if (fallthroughExceptions.isNotEmpty()) ", not $fallthroughExceptions" else ""))
}

data class STM(val initNode: Node, val edges: Set<Edge>) {
    init {
        val nodes = edges.map { listOf(it.source, it.target) }.flatten().toSet()
        nodes.forEach {
            check(
                it.parent == null || it.parent === this) { "Edges to behave encapsulated (offender: $it)" }
            it.parent = this
        }
    }

    private fun visualizeNodes(): String = edges.map { listOf(it.source, it.target) }.flatten()
        .toSet().map { it.visualize() }.reduce { a, b -> "$a\n$b" }

    fun visualize(): String = """
${visualizeNodes()}

[*] --> ${initNode.name}
${edges.map { it.visualize() }.reduce { a, b -> "$a\n$b" }}
""".trimMargin()

    fun execute(): Pair<Any, Any> {
        var currentNode: Node = initNode
        while (true) {
            try {
                return currentNode.execute()
            } catch (e: Exception) {
                println("Caught exception: $e")
                val edge: Edge? = currentNode.outEdges.find { it.trigger(e) }
                if (edge != null) {
                    currentNode = edge.target
                } else {
                    println("Could not handle trigger $e (Available triggers: ${
                        currentNode.outEdges.map { it.trigger }.toList()
                    })")
                    throw e
                }
            }
        }
    }
}

fun XcfaCegarConfig.visualize(inProcess: Boolean): String =
    """solvers: $abstractionSolver, $refinementSolver
    |domain: $domain, search: $search, initprec: $initPrec, por: $porLevel
    |refinement: $refinement, pruneStrategy: $pruneStrategy
    |timeout: $timeoutMs ms, inProcess: $inProcess""".trimMargin()