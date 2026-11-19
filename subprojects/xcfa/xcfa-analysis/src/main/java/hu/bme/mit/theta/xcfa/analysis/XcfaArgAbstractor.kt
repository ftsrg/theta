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
package hu.bme.mit.theta.xcfa.analysis

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.reachedset.Partition
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.common.logging.Logger
import java.util.function.Function
import java.util.stream.Collectors

class XcfaArgAbstractor<S : State, A : Action, P : Prec>(
  argBuilder: ArgBuilder<S, A, P>,
  projection: Function<in S?, *>?,
  waitlist: Waitlist<ArgNode<S, A>>,
  stopCriterion: StopCriterion<S, A>,
  logger: Logger,
) : BasicArgAbstractor<S, A, P>(argBuilder, projection, waitlist, stopCriterion, logger) {

  private val pops = LinkedHashMap<ArgNode<S, A>, Pop<ArgNode<S, A>>>()

  override fun check(arg: ARG<S, A>, prec: P): AbstractorResult {
    logger.write(Logger.Level.DETAIL, "|  |  Precision: %s%n", prec)

    if (!arg.isInitialized) {
      logger.write(Logger.Level.SUBSTEP, "|  |  (Re)initializing ARG...")
      argBuilder.init(arg, prec)
      logger.write(Logger.Level.SUBSTEP, "done%n")
    }

    assert(arg.isInitialized)

    logger.write(
      Logger.Level.INFO,
      "|  |  Starting ARG: %d nodes, %d incomplete, %d unsafe%n",
      arg.nodes.count(),
      arg.incompleteNodes.count(),
      arg.unsafeNodes.count(),
    )
    logger.write(Logger.Level.SUBSTEP, "|  |  Building ARG...")

    updatePops(arg)

    val reachedSet: Partition<ArgNode<S, A>, *> =
      Partition.of { n: ArgNode<S, A> -> projection.apply(n.state) }
    waitlist.clear()

    reachedSet.addAll(arg.nodes)
    waitlist.addAll(arg.incompleteNodes)

    if (!stopCriterion.canStop(arg)) {
      while (!waitlist.isEmpty) {
        val node = waitlist.remove()
        var newNodes: Collection<ArgNode<S, A>> = emptyList()
        val popSuccessors =
          if ((node.state as XcfaState<*>).xcfa!!.isInlined) {
            close(node, reachedSet[node])
            null
          } else {
            val expandProcedureCall = (node.state as XcfaState<*>) in (prec as XcfaPrec<P>).noPop
            closePop(arg, node, reachedSet[node], !expandProcedureCall, prec)
          }
        if (popSuccessors != null) {
          newNodes = popSuccessors
        } else if (!node.isSubsumed && !node.isTarget) {
          newNodes = argBuilder.expand(node, prec)
        }
        reachedSet.addAll(newNodes)
        waitlist.addAll(newNodes)
        if (stopCriterion.canStop(arg, newNodes)) break
      }
    }

    logger.write(Logger.Level.SUBSTEP, "done%n")
    logger.write(
      Logger.Level.INFO,
      "|  |  Finished ARG: %d nodes, %d incomplete, %d unsafe%n",
      arg.nodes.count(),
      arg.incompleteNodes.count(),
      arg.unsafeNodes.count(),
    )

    waitlist.clear() // Optimization

    return if (arg.isSafe) {
      Preconditions.checkState(arg.isComplete, "Returning incomplete ARG as safe")
      AbstractorResult.safe()
    } else {
      AbstractorResult.unsafe()
    }
  }

  /**
   * Covers [node] if possible. If not, it checks for stack cover and leaps to the end of the
   * current procedure with an edge havocing written globals and output variables then returns the
   * successors. Returns null otherwise.
   */
  fun closePop(
    arg: ARG<S, A>,
    node: ArgNode<S, A>,
    candidates: Collection<ArgNode<S, A>>,
    popCovered: Boolean,
    prec: P,
  ): Collection<ArgNode<S, A>>? {
    if (!node.isLeaf || node.isTarget) return null
    val state = node.state as XcfaState<*>
    val covering = candidates.filter { it.mayCover(node) }
    covering
      .firstOrNull { candidate -> state.processes == (candidate.state as XcfaState<*>).processes }
      ?.let {
        node.cover(it)
        return null
      }
    if (!popCovered) return null
    val stackCovering = covering.firstOrNull() ?: return null
    val (pid, process) =
      state.processes.entries.singleOrNull() ?: return null // no popping in concurrency
    val nextCnt = (state.sGlobal as? PtrState<*>)?.nextCnt ?: 0
    val actions = state.xcfa?.leapToReturn(pid, process, nextCnt) ?: return null
    val transFunc = argBuilder.analysis.transFunc
    val successors =
      actions.flatMap { action ->
        transFunc.getSuccStates(node.state, action as A, prec).map { succState ->
          arg.createSuccNode(node, action, succState, argBuilder.target.test(succState))
        }
      }
    node.expanded = true
    pops[node] = Pop(stackCovering, successors)
    return successors
  }

  /**
   * Updates [pops] if the node or its covering node has been pruned. Prunes successors in the
   * latter case.
   */
  private fun updatePops(arg: ARG<S, A>) {
    if (pops.isEmpty()) return
    val nodes = arg.nodes.collect(Collectors.toSet())
    pops.entries.removeIf { (node, pop) ->
      when {
        // remove if node has been pruned or is to be expanded
        node !in nodes || !node.isExpanded -> true
        // if covering node has been pruned, prune successors and remove
        pop.covering !in nodes -> {
          pop.successors.filter { it in nodes }.forEach(arg::prune)
          node.expanded = false
          true
        }
        // keep otherwise
        else -> false
      }
    }
  }

  private data class Pop<N>(val covering: N, val successors: List<N>)

  companion object {

    fun <S : State, A : Action, P : Prec> builder(
      argBuilder: ArgBuilder<S, A, P>
    ): BasicArgAbstractor.Builder<S, A, P> {
      return Builder(argBuilder)
    }
  }

  class Builder<S : State, A : Action, P : Prec>(argBuilder: ArgBuilder<S, A, P>) :
    BasicArgAbstractor.Builder<S, A, P>(argBuilder) {

    override fun build(): BasicArgAbstractor<S, A, P> {
      return XcfaArgAbstractor(argBuilder, projection, waitlist, stopCriterion, logger)
    }
  }
}
