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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction

import hu.bme.mit.theta.analysis.algorithm.asg.ASGEdge
import hu.bme.mit.theta.analysis.algorithm.asg.ASGNode
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger

/**
 * Both searches are iterative DFS: a shared path holds the edges from the initial node to the
 * current one, and a stack the unvisited out-edges of each node on it, so the depth is not bounded
 * by the call stack. The red search extends the blue path in place and restores it when it fails.
 */
object NdfsSearchStrategy : ILoopCheckerSearchStrategy {

  override fun <S : ExprState, A : ExprAction> search(
    initNodes: Collection<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): Collection<ASGTrace<S, A>> {
    for (node in initNodes) {
      for (edge in expand(node)) {
        val result = blueSearch(edge, mutableSetOf(), target, expand)
        if (!result.isEmpty()) return result
      }
    }
    return emptyList()
  }

  private fun <S : ExprState, A : ExprAction> redSearch(
    seed: ASGNode<S, A>,
    initEdge: ASGEdge<S, A>,
    path: MutableList<ASGEdge<S, A>>,
    expand: NodeExpander<S, A>,
  ): List<ASGEdge<S, A>>? {
    val redNodes: MutableSet<ASGNode<S, A>> = mutableSetOf()
    val stack = ArrayDeque<Iterator<ASGEdge<S, A>>>()
    var edge: ASGEdge<S, A>? = initEdge
    while (edge != null) {
      val targetNode = edge.target
      if (!targetNode.state.isBottom) {
        if (targetNode == seed && path.isNotEmpty()) {
          return path + edge
        }
        if (redNodes.add(targetNode)) {
          path.add(edge)
          stack.addLast(expand(targetNode).iterator())
        }
      }
      edge = stack.nextEdge(path)
    }
    return null
  }

  private fun <S : ExprState, A : ExprAction> blueSearch(
    initEdge: ASGEdge<S, A>,
    blueNodes: MutableSet<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
  ): Collection<ASGTrace<S, A>> {
    val path: MutableList<ASGEdge<S, A>> = mutableListOf()
    val stack = ArrayDeque<Iterator<ASGEdge<S, A>>>()
    var edge: ASGEdge<S, A>? = initEdge
    while (edge != null) {
      val targetNode = edge.target
      if (!targetNode.state.isBottom) {
        path.add(edge)
        if (target.test(Pair(targetNode.state, edge.action))) {
          // Edge source can only be null artificially, and is only used when calling other search
          // strategies
          val accNode = if (targetNode.accepting) targetNode else edge.source!!
          for (outEdge in expand(targetNode)) {
            val redSearch = redSearch(accNode, outEdge, path, expand)
            if (redSearch != null) return setOf(ASGTrace(redSearch, accNode))
          }
        }
        if (blueNodes.add(targetNode)) {
          stack.addLast(expand(targetNode).iterator())
        } else {
          path.removeAt(path.lastIndex)
        }
      }
      edge = stack.nextEdge(path)
    }
    return emptyList()
  }

  /**
   * Pops the exhausted nodes (and their incoming edge from [path]), returns the next edge, if any.
   */
  private fun <E> ArrayDeque<Iterator<E>>.nextEdge(path: MutableList<E>): E? {
    while (isNotEmpty()) {
      val outEdges = last()
      if (outEdges.hasNext()) return outEdges.next()
      removeLast()
      path.removeAt(path.lastIndex)
    }
    return null
  }
}
