/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

typealias BacktrackResult<S, A> = Pair<Set<ASGNode<S, A>>?, List<ASGTrace<S, A>>?>

fun <S : ExprState, A : ExprAction> combineLassos(results: Collection<BacktrackResult<S, A>>) =
  Pair(setOf<ASGNode<S, A>>(), results.flatMap { it.second ?: emptyList() })

abstract class AbstractSearchStrategy : ILoopcheckerSearchStrategy {

  internal fun <S : ExprState, A : ExprAction> expandFromInitNodeUntilTarget(
    initNode: ASGNode<S, A>,
    stopAtLasso: Boolean,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): Collection<ASGTrace<S, A>> {
    return expandThroughNode(
        emptyMap(),
        ASGEdge(null, initNode, null, false),
        emptyList(),
        0,
        stopAtLasso,
        expand,
        logger,
      )
      .second!!
  }

  private fun <S : ExprState, A : ExprAction> expandThroughNode(
    pathSoFar: Map<ASGNode<S, A>, Int>,
    incomingEdge: ASGEdge<S, A>,
    edgesSoFar: List<ASGEdge<S, A>>,
    targetsSoFar: Int,
    stopAtLasso: Boolean,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): BacktrackResult<S, A> {
    val expandingNode: ASGNode<S, A> = incomingEdge.target
    logger.write(
      Logger.Level.VERBOSE,
      "Expanding through %s edge to %s node with state %s%n",
      if (incomingEdge.accepting) "accepting" else "not accepting",
      if (expandingNode.accepting) "accepting" else "not accepting",
      expandingNode.state,
    )
    if (expandingNode.state.isBottom()) {
      logger.write(Logger.Level.VERBOSE, "Node is a dead end since its bottom%n")
      return BacktrackResult(null, null)
    }
    val totalTargets =
      if (expandingNode.accepting || incomingEdge.accepting) targetsSoFar + 1 else targetsSoFar
    if (pathSoFar.containsKey(expandingNode) && pathSoFar[expandingNode]!! < totalTargets) {
      logger.write(
        Logger.Level.SUBSTEP,
        "Found trace with a length of %d, building lasso...%n",
        pathSoFar.size,
      )
      logger.write(Logger.Level.DETAIL, "Honda should be: %s", expandingNode.state)
      pathSoFar.forEach { (node, targetsThatFar) ->
        logger.write(
          Logger.Level.VERBOSE,
          "Node state %s | targets that far: %d%n",
          node.state,
          targetsThatFar,
        )
      }
      val lasso: ASGTrace<S, A> = ASGTrace(edgesSoFar + incomingEdge, expandingNode)
      logger.write(Logger.Level.DETAIL, "Built the following lasso:%n")
      lasso.print(logger, Logger.Level.DETAIL)
      return BacktrackResult(null, listOf(lasso))
    }
    if (pathSoFar.containsKey(expandingNode)) {
      logger.write(Logger.Level.VERBOSE, "Reached loop but no acceptance inside%n")
      return BacktrackResult(setOf(expandingNode), null)
    }
    val needsTraversing =
      !expandingNode.expanded ||
        expandingNode.validLoopHondas.filter(pathSoFar::containsKey).any {
          pathSoFar[it]!! < targetsSoFar
        }
    val expandStrategy: NodeExpander<S, A> =
      if (needsTraversing) expand else { _ -> mutableSetOf() }
    val outgoingEdges: Collection<ASGEdge<S, A>> = expandStrategy(expandingNode)
    val results: MutableList<BacktrackResult<S, A>> = mutableListOf()
    for (newEdge in outgoingEdges) {
      val result: BacktrackResult<S, A> =
        expandThroughNode(
          pathSoFar + (expandingNode to totalTargets),
          newEdge,
          if (incomingEdge.source != null) edgesSoFar.plus(incomingEdge) else edgesSoFar,
          totalTargets,
          stopAtLasso,
          expand,
          logger,
        )
      results.add(result)
      if (stopAtLasso && result.second?.isNotEmpty() == true) break
    }
    val result: BacktrackResult<S, A> = combineLassos(results)
    if (result.second != null) return result
    val validLoopHondas: Collection<ASGNode<S, A>> = results.flatMap { it.first ?: emptyList() }
    expandingNode.validLoopHondas.addAll(validLoopHondas)
    return BacktrackResult(validLoopHondas.toSet(), null)
  }
}

object GdfsSearchStrategy : AbstractSearchStrategy() {

  override fun <S : ExprState, A : ExprAction> search(
    initNodes: Collection<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): Collection<ASGTrace<S, A>> {
    for (initNode in initNodes) {
      val possibleTraces: Collection<ASGTrace<S, A>> =
        expandFromInitNodeUntilTarget(initNode, true, expand, logger)
      if (!possibleTraces.isEmpty()) {
        return possibleTraces
      }
    }
    return emptyList()
  }
}

object FullSearchStrategy : AbstractSearchStrategy() {

  override fun <S : ExprState, A : ExprAction> search(
    initNodes: Collection<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ) = initNodes.flatMap { expandFromInitNodeUntilTarget(it, false, expand, logger) }
}
