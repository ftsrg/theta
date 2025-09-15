/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.algorithm.Result
import hu.bme.mit.theta.xcfa.cli.params.Backend
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig

abstract class Node(val name: String) {

  val outEdges: MutableSet<Edge> = LinkedHashSet()
  var parent: STM? = null

  abstract fun execute(): Pair<Any, Any>

  abstract fun visualize(): String
}

class HierarchicalNode(name: String, val innerSTM: STM) : Node(name) {

  override fun execute(): Pair<Any, Any> = innerSTM.execute()

  override fun visualize(): String =
    """state $name {
${innerSTM.visualize()}
}"""
      .trimIndent()
}

fun XcfaConfig<*, *>.visualize(): String =
  if (backendConfig.backend == Backend.BOUNDED) {
    val specConfig = backendConfig.specConfig as BoundedConfig
    """
      reversed: ${specConfig.reversed}
      abstract: ${specConfig.cegar}
      bmc: ${!specConfig.bmcConfig.disable}
      bmcSolver: ${specConfig.bmcConfig.bmcSolver}
      kind: ${!specConfig.indConfig.disable}
      kindSolver: ${specConfig.indConfig.indSolver}
      imc: ${!specConfig.itpConfig.disable}
      imcSolver: ${specConfig.itpConfig.itpSolver}
    """
      .trimIndent()
  } else {
    ""
  }

class ConfigNode(
  name: String,
  private val config: XcfaConfig<*, *>,
  private val check: (config: XcfaConfig<*, *>) -> Result<*>,
) : Node(name) {

  override fun execute(): Pair<Any, Any> {
    println("Current configuration: $config")
    return Pair(Pair(name, config), check(config))
  }

  override fun visualize(): String =
    config
      .visualize()
      .lines() // TODO: reintroduce visualize()
      .map { "state ${name.replace(Regex("[:\\.-]+"), "_")}: $it" }
      .reduce { a, b -> "$a\n$b" }
}

data class Edge(
  val source: Node,
  val target: Node,
  val trigger: (Throwable) -> Boolean,
  val guard: (Node, Edge) -> Boolean = { _, _ -> true },
) {

  init {
    source.outEdges.add(this)
  }

  fun visualize(): String =
    """${source.name.replace(Regex("[:\\.-]+"), "_")} --> ${
        target.name.replace(Regex("[:\\.-]+"), "_")
    } : $trigger """
}

// if the exceptions set is empty, it catches all exceptions
class ExceptionTrigger(
  val exceptions: Set<Throwable> = emptySet(),
  val fallthroughExceptions: Set<Throwable> = emptySet(),
  val label: String? = null,
) : (Throwable) -> Boolean {

  constructor(
    vararg exceptions: Throwable,
    label: String? = null,
  ) : this(exceptions.toSet(), label = label)

  override fun invoke(e: Throwable): Boolean =
    if (exceptions.isNotEmpty()) exceptions.contains(e) && !fallthroughExceptions.contains(e)
    else !fallthroughExceptions.contains(e)

  override fun toString(): String =
    label
      ?: ((if (exceptions.isNotEmpty()) exceptions.toString() else "*") +
        (if (fallthroughExceptions.isNotEmpty()) ", not $fallthroughExceptions" else ""))
}

data class STM(val initNode: Node, val edges: Set<Edge>) {
  init {
    val nodes = edges.map { listOf(it.source, it.target) }.flatten().toSet()
    nodes.forEach {
      check(it.parent == null || it.parent === this) {
        "Edges to behave encapsulated (offender: $it)"
      }
      it.parent = this
    }
  }

  private fun visualizeNodes(): String {
    val lastNodes = mutableSetOf<Node>()
    val nodes = mutableSetOf(initNode)
    while (!lastNodes.containsAll(nodes)) {
      lastNodes.addAll(nodes)
      nodes.addAll(nodes.flatMap { it.outEdges.map { it.target } })
    }
    return nodes.map { it.visualize() }.reduce { a, b -> "$a\n$b" }
  }

  fun visualize(): String =
    """
${visualizeNodes()}

[*] --> ${initNode.name.replace(Regex("[:\\.-]+"), "_")}
${edges.map { it.visualize() }.reduce { a, b -> "$a\n$b" }}
"""
      .trimMargin()

  fun execute(): Pair<Any, Any> {
    var currentNode: Node = initNode
    while (true) {
      try {
        return currentNode.execute()
      } catch (e: Throwable) {
        println("Caught exception: $e")
        val edge: Edge? = currentNode.outEdges.find { it.trigger(e) }
        if (edge != null) {
          println("Handling exception as ${edge.trigger}")
          currentNode = edge.target
        } else {
          println(
            "Could not handle trigger $e (Available triggers: ${
                        currentNode.outEdges.map { it.trigger }.toList()
                    })"
          )
          throw e
        }
      }
    }
  }
}

// fun XcfaConfig<*, CegarConfig>.visualize(inProcess: Boolean): String =
//    """solvers: $abstractionSolver, $refinementSolver
//    |domain: $domain, search: $search, initprec: $initPrec, por: $porLevel
//    |refinement: $refinement, pruneStrategy: $pruneStrategy
//    |timeout: $timeoutMs ms, inProcess: $inProcess""".trimMargin()
