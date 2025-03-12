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
package hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace

class AbstractSummaryBuilder<S : State, A : Action> {
  val argTraces: MutableList<ArgTrace<S, A>> = mutableListOf()

  fun addTrace(trace: ArgTrace<S, A>) {
    if (argTraces.isNotEmpty()) {
      checkState(
        argTraces.get(0).node(0) == trace.node(0),
        "All traces in summary must start with the same node!",
      )
    }
    argTraces.add(trace)
  }

  fun build(): AbstractTraceSummary<S, A> {
    checkState(argTraces.isNotEmpty(), "Summary must have at least one trace in it!")

    val argNodes: Set<ArgNode<S, A>> = argTraces.map { trace -> trace.nodes() }.flatten().toSet()

    // grouping nodes covering each other for state summaries
    val nodeGroups: MutableList<MutableSet<ArgNode<S, A>>> = mutableListOf()
    for (node in argNodes) {
      if (nodeGroups.isEmpty()) {
        nodeGroups.add(mutableSetOf(node))
      } else {
        val inCoverRelationWithNode: MutableList<ArgNode<S, A>> = mutableListOf()
        inCoverRelationWithNode.addAll(node.coveredNodes.toList())
        if (node.coveringNode.isPresent) inCoverRelationWithNode.add(node.coveringNode.get())

        val nodeGroup =
          nodeGroups
            .filter(
              fun(group: MutableSet<ArgNode<S, A>>): Boolean {
                for (coverNode in inCoverRelationWithNode) {
                  if (group.contains(coverNode)) {
                    return true
                  }
                }
                return false
              }
            )
            .toList()

        checkState(
          nodeGroup.size <= 1
        ) // either found one where node would fit OR found none and will create new one
        if (nodeGroup.size > 0) {
          nodeGroup[0].add(node)
        } else {
          nodeGroups.add(mutableSetOf(node))
        }
      }
    }

    // create summary nodes and a map of argnodes to summary nodes
    val argNodeSummaryNodeMap =
      nodeGroups
        .flatMap { AbstractSummaryNode.create(it) } // Create summary nodes for each group
        .flatMap { summaryNode -> summaryNode.argNodes.map { node -> node to summaryNode } }
        .toMap()

    val summaryNodes = argNodeSummaryNodeMap.values.toSet()
    val initSummaryNodes =
      summaryNodes.filter { summaryNode -> argTraces.get(0).node(0) in summaryNode.argNodes }
    checkState(initSummaryNodes.size == 1, "Initial arg node must be in exactly 1 summary node!")
    val initNode = initSummaryNodes.get(0)

    val abstractSummaryEdges = mutableSetOf<AbstractSummaryEdge<S, A>>()
    // save edges as well, so we can easily connect edge sources and targets
    for (summaryNode in summaryNodes) {
      for (argNode in summaryNode.argNodes) {
        for (edge in argNode.outEdges) {
          if (edge.target in argNodes) {
            // summary edge adds itself to source and target as well
            abstractSummaryEdges.add(
              AbstractSummaryEdge.create(edge, summaryNode, argNodeSummaryNodeMap[edge.target]!!)
            )
          }
        }
      }
    }

    return AbstractTraceSummary(argTraces, abstractSummaryEdges, summaryNodes, initNode)
  }
}

/**
 * This class represents an automata, similar to an ARG, where covered and covering nodes are merged
 * into a single node (which we thus call a summary node). In some sense this class represents a
 * wrapper level over a set of arg traces.
 */
data class AbstractTraceSummary<S : State, A : Action>(
  val sourceTraces: Collection<ArgTrace<S, A>>,
  val abstractSummaryEdges: Collection<AbstractSummaryEdge<S, A>>,
  val summaryNodes: Collection<AbstractSummaryNode<S, A>>,
  val initNode: AbstractSummaryNode<S, A>,
) : Proof {}

/**
 * Groups arg nodes based on coverages, but also stores the traces they appear in, coverage
 * relations and arg nodes
 */
class AbstractSummaryNode<S : State, A : Action>
private constructor(
  val id: Long,
  val argNodes: Set<ArgNode<S, A>>,
  val leastOverApproximatedNode: ArgNode<S, A>,
  val mostOverApproximatedNode: ArgNode<S, A>,
) {
  // not immutable for edges, as both source and target has to exist when creating edge :c
  var inEdges: MutableSet<AbstractSummaryEdge<S, A>> = mutableSetOf()
  var outEdges: MutableSet<AbstractSummaryEdge<S, A>> = mutableSetOf()

  companion object {
    var counter: Long = 0

    fun <S : State, A : Action> create(
      argNodes: MutableSet<ArgNode<S, A>>
    ): Set<AbstractSummaryNode<S, A>> {
      // all of the nodes should be in some kind of coverage relationship with each other,
      // so we partition them in a way that that is true
      val partitions = partitionNodes(argNodes)
      assert(partitions.size > 0)
      if (partitions.size > 1) {
        val abstractSummaryNodes = mutableSetOf<AbstractSummaryNode<S, A>>()
        for (partition in partitions) {
          abstractSummaryNodes.addAll(create(partition.toMutableSet()))
        }
        return abstractSummaryNodes
      } else {
        val notCoveredNodes = argNodes.filter { argNode -> argNode.coveringNode.isEmpty }
        var leastOverApproximatedNode =
          notCoveredNodes[0] // just get one of them, does not matter, which

        for (node in notCoveredNodes) {
          if (leastOverApproximatedNode != node) {
            // ancestors irrelevant here, subsumed should not be checked
            if (node.inPartialOrder(leastOverApproximatedNode)) {
              // node can cover the so far "least over approximated" node - node is more "abstract"
              leastOverApproximatedNode = node
            } else if (!leastOverApproximatedNode.inPartialOrder(node)) {
              throw RuntimeException(
                "All nodes in summary node should be in some partial ordering!"
              )
            }
          }
        }

        val notCoveringNodes =
          argNodes.filter { argNode ->
            argNode.coveredNodes.filter { node -> node in argNodes }.count() == 0L
          }
        var mostOverApproximatedNode = notCoveringNodes[0]

        for (node in notCoveringNodes) {
          if (mostOverApproximatedNode != node) {
            // ancestors irrelevant here, subsumed should not be checked
            if (mostOverApproximatedNode.inPartialOrder(node)) {
              // so far "most over approximated" node can cover this node - this node is more
              // abstract
              mostOverApproximatedNode = node
            } else if (!node.inPartialOrder(mostOverApproximatedNode)) {
              throw RuntimeException(
                "All nodes in summary node should be in some partial ordering!"
              )
            }
          }
        }

        return setOf(
          AbstractSummaryNode(
            counter++,
            argNodes,
            leastOverApproximatedNode,
            mostOverApproximatedNode,
          )
        )
      }
    }

    private fun <S : State, A : Action> partitionNodes(
      argNodes: Set<ArgNode<S, A>>
    ): List<Set<ArgNode<S, A>>> {
      // Build the adjacency list
      val graph =
        argNodes.associateWith { node ->
          argNodes
            .filter { it != node && (node.inPartialOrder(it) || it.inPartialOrder(node)) }
            .toSet()
        }

      // Find connected components using DFS
      val visited = mutableSetOf<ArgNode<S, A>>()
      val partitions = mutableListOf<Set<ArgNode<S, A>>>()

      fun dfs(node: ArgNode<S, A>, component: MutableSet<ArgNode<S, A>>) {
        if (node in visited) return
        visited += node
        component += node
        graph[node]?.forEach { dfs(it, component) }
      }

      for (node in argNodes) {
        if (node !in visited) {
          val component = mutableSetOf<ArgNode<S, A>>()
          dfs(node, component)
          partitions += component
        }
      }

      return partitions
    }
  }

  fun getStates(): Set<S> {
    return argNodes.map { argNode -> argNode.state }.toSet()
  }

  fun getLabel(): String {
    val sb = StringBuilder()

    for (node in argNodes) {
      val label = node.state.toString()
      if (label !in sb) {
        sb.append(label)
      }
    }

    return sb.toString()
  }

  override fun toString(): String {
    return getLabel()
  }

  fun addOutEdge(abstractSummaryEdge: AbstractSummaryEdge<S, A>) {
    outEdges.add(abstractSummaryEdge)
  }

  fun addInEdge(abstractSummaryEdge: AbstractSummaryEdge<S, A>) {
    inEdges.add(abstractSummaryEdge)
  }
}

class AbstractSummaryEdge<S : State, A : Action>
private constructor(
  val argEdge: ArgEdge<S, A>,
  val source: AbstractSummaryNode<S, A>,
  val target: AbstractSummaryNode<S, A>,
  val action: A = argEdge.action,
) {
  companion object {
    fun <S : State, A : Action> create(
      argEdge: ArgEdge<S, A>,
      source: AbstractSummaryNode<S, A>,
      target: AbstractSummaryNode<S, A>,
    ): AbstractSummaryEdge<S, A> {
      val abstractSummaryEdge = AbstractSummaryEdge(argEdge, source, target)
      source.addOutEdge(abstractSummaryEdge)
      target.addInEdge(abstractSummaryEdge)
      return abstractSummaryEdge
    }
  }

  fun getLabel(): String {
    return argEdge.action.toString()
  }
}
