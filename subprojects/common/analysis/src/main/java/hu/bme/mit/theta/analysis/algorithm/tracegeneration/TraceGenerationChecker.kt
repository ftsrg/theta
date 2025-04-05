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
package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.*
import hu.bme.mit.theta.analysis.algorithm.*
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractSummaryBuilder
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.TraceGenerationResult
import hu.bme.mit.theta.common.logging.Logger
import java.util.function.Consumer

class TraceGenerationChecker<S : State, A : Action, P : Prec>(
  private val logger: Logger,
  private val abstractor: BasicArgAbstractor<S, A, P>,
  private val getFullTraces: Boolean,
) : Checker<AbstractTraceSummary<S, A>, P> {
  private var traces: List<Trace<S, A>> = ArrayList()

  companion object {
    fun <S : State, A : Action, P : Prec> create(
      logger: Logger,
      abstractor: BasicArgAbstractor<S, A, P>,
      getFullTraces: Boolean,
    ): TraceGenerationChecker<S, A, P> {
      return TraceGenerationChecker(logger, abstractor, getFullTraces)
    }
  }

  override fun check(prec: P): TraceGenerationResult<AbstractTraceSummary<S, A>, S, A> {
    logger.write(
      Logger.Level.SUBSTEP,
      "Printing prec for trace generation...\n" + System.lineSeparator(),
    )
    logger.write(Logger.Level.SUBSTEP, prec.toString())

    val arg = abstractor.createProof()
    abstractor.check(arg, prec)
    logger.write(Logger.Level.SUBSTEP, "ARG done, fetching traces...\n")

    // bad node: mostly XSTS specific thing, that the last state (last_env nodes) doubles up and the
    // leaf is covered by the
    // last_env before which is superfluous.
    // Possible side effect if not handled: possibly a "non-existing leaf" and superfluous traces or
    // just traces that are 1 longer than they should be
    val badNodes = DoubleEndNodeRemover.collectBadLeaves(arg)
    logger.write(Logger.Level.INFO, "Number of bad nodes filtered out: ${badNodes.size}")

    // leaves
    val endNodes = arg.nodes.filter { obj: ArgNode<S, A> -> obj.isLeaf }.toList()
    // leaves, but bad nodes are properly filtered, see bad nodes above
    val filteredEndNodes = filterEndNodes(endNodes, badNodes)

    val argTraces: List<ArgTrace<S, A>> =
      ArrayList(
        filteredEndNodes.stream().map { node: ArgNode<S, A>? -> ArgTrace.to(node) }.toList()
      )

    assert(!getFullTraces)
    val summaryBuilder = AbstractSummaryBuilder<S, A>()
    argTraces.forEach { trace -> summaryBuilder.addTrace(trace) }
    val traceSetSummary = summaryBuilder.build()

    logger.write(Logger.Level.SUBSTEP, "-- Trace generation done --\n")

    return TraceGenerationResult(traceSetSummary)
  }

  private fun filterEndNodes(
    endNodes: List<ArgNode<S, A>>,
    badNodes: List<ArgNode<S, A>>,
  ): List<ArgNode<S, A>> {
    val filteredEndNodes: MutableList<ArgNode<S, A>> =
      ArrayList() // leaves that are not "bad nodes" or that are bad nodes' grandparents
    endNodes.forEach(
      Consumer { endNode: ArgNode<S, A> ->
        if (badNodes.contains(endNode)) {
          if (endNode.parent.isPresent && endNode.parent.get().parent.isPresent) {
            val parent = endNode.parent.get()
            val grandParent = endNode.parent.get().parent.get()
            // If the parent & grandparent (same state as the bad node) has no other successors,
            // the grandparent is the "new leaf"
            // if there are other successors, there is no real leaf here
            val goodGrandparentSuccessors =
              grandParent.outEdges
                .flatMap { it.target.outEdges }
                .filter { !badNodes.contains(it.target) }
                .count()
            val goodParentSuccessors =
              parent.outEdges.filter { !badNodes.contains(it.target) }.count()
            if (goodGrandparentSuccessors == 0L && goodParentSuccessors == 0L) {
              filteredEndNodes.add(grandParent)
            }
          } else {
            throw RuntimeException(
              "Unexpected error: bad nodes should always have parents and grandparents"
            )
          }
        } else {
          filteredEndNodes.add(endNode)
        }
      }
    )

    return filteredEndNodes
  }

  private fun computeCrossCoveredEndNodes(
    filteredEndNodes: List<ArgNode<S, A>>
  ): List<ArgNode<S, A>> {
    val coveredEndNodes: MutableList<ArgNode<S, A>> = ArrayList()
    for (node in filteredEndNodes) {
      if (node.isCovered) {
        // and covered-by edge is a cross-edge:
        val coveringNode = node.coveringNode.get() // check above with isCovered()
        var parentNode = node.parent
        var crossEdge = true
        while (parentNode.isPresent) {
          if (parentNode.get() == coveringNode) {
            // not a cross edge
            crossEdge = false
            break
          }
          parentNode = parentNode.get().parent
        }

        if (crossEdge) {
          coveredEndNodes.add(node)
        }
      }
    }
    return coveredEndNodes
  }

  /*
  private fun modifyToFullTraces(
      filteredEndNodes: List<ArgNode<S, A>>,
      argTraces: List<ArgTrace<S, A>>
  ): List<Trace<S, A>> {
      val crossCoveredEndNodes = computeCrossCoveredEndNodes(filteredEndNodes)
      // new traces
      var newTraces: MutableList<List<AdvancedArgTrace<S, A>>> = ArrayList() // T'
      for (argTrace in argTraces) {
          newTraces.add(java.util.List.of(AdvancedArgTrace.to(argTrace.node(argTrace.nodes().size - 1))))
      }

      // now we iterate over the new traces until all of them are maximal
      // TODO - lengthening the traces this way is far from being the most efficient, it can easily blow up
      // some kind of smart collecting of partial traces "globally", instead of iteratively and then pairing all of
      // them properly might be faster (not sure)
      // but however we do this, the number of full traces in the result can easily blow up anyways, so I am not sure
      // it would matter much
      var tracesChanged = true
      while (tracesChanged) {
          tracesChanged = false
          val changedTraces: MutableList<List<AdvancedArgTrace<S, A>>> = ArrayList() // T''
          for (newTrace in newTraces) {
              val lastNode = getLastNode(newTrace)
              if (crossCoveredEndNodes.contains(lastNode)) { // isCovered() check present
                  val coveringNode = lastNode.coveringNode.get()
                  // we can lengthen the new trace more
                  // and it can even branch, so we might add several new traces actually
                  // for (ArgTrace<S, A> existingTrace : argTraces) {
                  for (existingTrace in argTraces) {
                      if (existingTrace.nodes().contains(coveringNode)) {
                          // getting a new part for the trace
                          val newPart = AdvancedArgTrace.fromTo(
                              coveringNode,
                              existingTrace.node(existingTrace.nodes().size - 1)
                          )
                          val newPartLastNode = newPart.node(newPart.nodes().size - 1)
                          if (newPartLastNode.isCovered && !crossCoveredEndNodes.contains(
                                  newPartLastNode
                              )
                          ) {
                              tracesChanged = false
                          } else {
                              tracesChanged = true
                              val changedTrace = ArrayList(newTrace)
                              changedTrace.add(newPart)
                              changedTraces.add(changedTrace)
                          }
                      }
                  }
              } else {
                  changedTraces.add(newTrace)
              }
          }

          if (tracesChanged) {
              newTraces = changedTraces
          }
      }

      val result: MutableList<Trace<S, A>> = ArrayList() // TODO should be a Set(?)
      // concatenating lengthened maximal traces and converting them to state-action traces to add them to the result list
      for (newTrace in newTraces) {
          result.add(concatenateTraces(newTrace))
      }

      // adding traces that did not have to be lengthened to the resulting state-action trace list
      */
  /*
  for (ArgTrace<S, A> argTrace : argTraces) {
      if(!crossCoveredEndNodes.contains(argTrace.node(argTrace.nodes().size()-1))) {
          result.add(argTrace.toTrace());
      }
  }
  */
  /*

          return result
      }
  */

  // created for traces that are stored as a list (they are not concatenated yet)
  private fun getLastNode(traceList: List<AdvancedArgTrace<S, A>>): ArgNode<S, A> {
    val traces = traceList[traceList.size - 1]
    return traces.node(traces.nodes().size - 1)
  }

  private fun concatenateTraces(parts: List<AdvancedArgTrace<S, A>>): Trace<S, A> {
    Preconditions.checkState(parts.size > 0)
    val newTraceStates = ArrayList<S>()
    val newTraceActions = ArrayList<A>()
    for (part in parts) {
      // Concatenating states
      if (newTraceStates.size > 0) {
        newTraceStates.removeAt(newTraceStates.size - 1)
      }
      newTraceStates.addAll(part.toTrace().states)

      // Concatenating actions
      newTraceActions.addAll(part.toTrace().actions)
    }

    return Trace.of(newTraceStates, newTraceActions)
  }
}
