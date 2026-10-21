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

typealias BacktrackResult<S, A> = Pair<Set<ASGNode<S, A>>?, List<ASGTrace<S, A>>?>

fun <S : ExprState, A : ExprAction> combineLassos(results: Collection<BacktrackResult<S, A>>) =
  Pair(setOf<ASGNode<S, A>>(), results.flatMap { it.second ?: emptyList() })

abstract class AbstractSearchStrategy : ILoopCheckerSearchStrategy {

  internal fun <S : ExprState, A : ExprAction> expandFromInitNodeUntilTarget(
    initNode: ASGNode<S, A>,
    stopAtLasso: Boolean,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): Collection<ASGTrace<S, A>> {
    return ExpansionSearch(stopAtLasso, expand, logger)
      .expandThroughNode(ASGEdge(null, initNode, null, false))
      .second!!
  }
}

private class ExpansionFrame<S : ExprState, A : ExprAction>(
  val expandingNode: ASGNode<S, A>,
  val totalTargets: Int,
  val addedIncomingEdge: Boolean,
  val outgoingEdges: Iterator<ASGEdge<S, A>>,
) {
  val results: MutableList<BacktrackResult<S, A>> = mutableListOf()
}

/**
 * A depth-first expansion unrolled onto an explicit [stack] of frames, so the depth is not bounded
 * by the call stack. [pathSoFar] and [edgesSoFar] are shared and always describe the path of the
 * frames on the stack; [enter] and [leave] are the parts of a visit before and after its children.
 */
private class ExpansionSearch<S : ExprState, A : ExprAction>(
  private val stopAtLasso: Boolean,
  private val expand: NodeExpander<S, A>,
  private val logger: Logger,
) {

  private val pathSoFar: MutableMap<ASGNode<S, A>, Int> = linkedMapOf()
  private val edgesSoFar: MutableList<ASGEdge<S, A>> = mutableListOf()
  private val stack = ArrayDeque<ExpansionFrame<S, A>>()

  fun expandThroughNode(initEdge: ASGEdge<S, A>): BacktrackResult<S, A> {
    var result: BacktrackResult<S, A>? = enter(initEdge, 0)
    while (true) {
      if (result == null) {
        val frame = stack.last()
        result =
          if (frame.outgoingEdges.hasNext()) enter(frame.outgoingEdges.next(), frame.totalTargets)
          else leave()
        continue
      }
      val parent = stack.lastOrNull() ?: return result
      parent.results.add(result)
      result = if (stopAtLasso && result.second?.isNotEmpty() == true) leave() else null
    }
  }

  /** Returns the result of visiting [incomingEdge]'s target, or null if it pushed a frame. */
  private fun enter(incomingEdge: ASGEdge<S, A>, targetsSoFar: Int): BacktrackResult<S, A>? {
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
    pathSoFar[expandingNode] = totalTargets
    val addedIncomingEdge = incomingEdge.source != null
    if (addedIncomingEdge) edgesSoFar.add(incomingEdge)
    stack.addLast(
      ExpansionFrame(expandingNode, totalTargets, addedIncomingEdge, outgoingEdges.iterator())
    )
    return null
  }

  /** Pops the top frame and returns the result of its visit. */
  private fun leave(): BacktrackResult<S, A> {
    val frame = stack.removeLast()
    pathSoFar.remove(frame.expandingNode)
    if (frame.addedIncomingEdge) edgesSoFar.removeAt(edgesSoFar.lastIndex)
    val results = frame.results
    val result: BacktrackResult<S, A> = combineLassos(results)
    if (result.second != null) return result
    val validLoopHondas: Collection<ASGNode<S, A>> = results.flatMap { it.first ?: emptyList() }
    frame.expandingNode.validLoopHondas.addAll(validLoopHondas)
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
