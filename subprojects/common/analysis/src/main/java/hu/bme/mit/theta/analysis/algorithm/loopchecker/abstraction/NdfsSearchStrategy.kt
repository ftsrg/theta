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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction

import hu.bme.mit.theta.analysis.algorithm.asg.ASGEdge
import hu.bme.mit.theta.analysis.algorithm.asg.ASGNode
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger

object NdfsSearchStrategy : ILoopCheckerSearchStrategy {

  override fun <S : ExprState, A : ExprAction> search(
    initNodes: Collection<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): Collection<ASGTrace<S, A>> {
    for (node in initNodes) {
      for (edge in expand(node)) {
        val result = blueSearch(edge, emptyList(), mutableSetOf(), mutableSetOf(), target, expand)
        if (!result.isEmpty()) return result
      }
    }
    return emptyList()
  }

  private fun <S : ExprState, A : ExprAction> redSearch(
    seed: ASGNode<S, A>,
    edge: ASGEdge<S, A>,
    trace: List<ASGEdge<S, A>>,
    redNodes: MutableSet<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
  ): List<ASGEdge<S, A>> {
    val targetNode = edge.target
    if (targetNode.state.isBottom) {
      return emptyList()
    }
    if (targetNode == seed && trace.isNotEmpty()) {
      return trace + edge
    }
    if (redNodes.contains(targetNode)) {
      return emptyList()
    }
    redNodes.add(edge.target)
    for (nextEdge in expand(targetNode)) {
      val redSearch: List<ASGEdge<S, A>> =
        redSearch(seed, nextEdge, trace + edge, redNodes, target, expand)
      if (redSearch.isNotEmpty()) return redSearch
    }
    return emptyList()
  }

  private fun <S : ExprState, A : ExprAction> blueSearch(
    edge: ASGEdge<S, A>,
    trace: List<ASGEdge<S, A>>,
    blueNodes: MutableSet<ASGNode<S, A>>,
    redNodes: Set<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
  ): Collection<ASGTrace<S, A>> {
    val targetNode = edge.target
    if (targetNode.state.isBottom) {
      return emptyList()
    }
    if (target.test(Pair(targetNode.state, edge.action))) {
      // Edge source can only be null artificially, and is only used when calling other search
      // strategies
      val accNode = if (targetNode.accepting) targetNode else edge.source!!
      for (outEdge in expand(edge.target)) {
        val redSearch: List<ASGEdge<S, A>> =
          redSearch(accNode, outEdge, trace + edge, mutableSetOf(), target, expand)
        if (redSearch.isNotEmpty()) return setOf(ASGTrace(redSearch, accNode))
      }
    }
    if (blueNodes.contains(targetNode)) {
      return emptyList()
    }
    blueNodes.add(edge.target)
    for (nextEdge in expand(targetNode)) {
      val blueSearch: Collection<ASGTrace<S, A>> =
        blueSearch(nextEdge, trace + edge, blueNodes, redNodes, target, expand)
      if (blueSearch.isNotEmpty()) return blueSearch
    }
    return emptyList()
  }
}
