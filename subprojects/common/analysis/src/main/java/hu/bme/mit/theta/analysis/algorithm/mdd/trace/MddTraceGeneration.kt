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
package hu.bme.mit.theta.analysis.algorithm.mdd.trace

import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddSignature
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.splitAction
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodePostcondition
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.ReverseNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SingleStepProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.TraceProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.stopwatch.Stopwatch
import hu.bme.mit.theta.core.utils.PathUtils
import java.util.concurrent.ExecutionException
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

/**
 * How the counterexample is searched: DFS takes an arbitrary predecessor per step (its length
 * depends on the variable order), BFS builds forward layers from the initial states and
 * BFS_BACKWARD backward layers from the violating states; both give a shortest counterexample.
 */
enum class TraceSearch {
  DFS,
  BFS,
  BFS_BACKWARD,
}

/**
 * Trace generation shared by [hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker] and
 * [hu.bme.mit.theta.analysis.algorithm.mdd.cegar.MddCegarChecker]: searches the computed state
 * space from [propViolating] back to [initNode]; each step carries the action of the transition
 * (index into [MonolithicExpr.split] and [transNodes]) that fired. Null if not finished within
 * [traceTimeout] seconds.
 */
internal fun generateTrace(
  transNodes: List<MddHandle>,
  transSig: MddSignature,
  stateSpace: MddHandle,
  propViolating: MddHandle,
  initNode: MddHandle,
  stateSig: MddSignature,
  model: MonolithicExpr,
  traceTimeout: Long,
  logger: Logger,
  search: TraceSearch = TraceSearch.DFS,
): Trace<ExplState, ExprAction>? {
  // an initially violating state must be the seed, or the collector may pick a non-initial one
  val initViolating = propViolating.intersection(initNode)
  val traceSeed =
    if (MddInterpreter.calculateNonzeroCount(initViolating) > 0) initViolating else propViolating

  val executor = Executors.newSingleThreadExecutor()
  val future =
    executor.submit<Trace<ExplState, ExprAction>> {
      val mirrorTop = MddExplicitRepresentationExtractor.mirrorTopOf(transSig.topVariableHandle)
      val explicitTrans =
        transNodes.map { MddExplicitRepresentationExtractor.transform(it, mirrorTop) }
      val forward = explicitTrans.map { MddNodeNextStateDescriptor.of(it) }
      val orReversed =
        OrNextStateDescriptor.create(
          explicitTrans.map { ReverseNextStateDescriptor.of(stateSpace, it) }
        )
      val top = stateSig.topVariableHandle

      val traceProvider = TraceProvider(stateSig.variableOrder)
      val stepper = SingleStepProvider(stateSig.variableOrder)
      val states = ArrayList<MddHandle>()
      val actions = ArrayList<ExprAction>()
      try {
        val layers =
          when (search) {
            TraceSearch.DFS -> traceProvider.compute(traceSeed, orReversed, initNode, top)
            TraceSearch.BFS ->
              forwardBreadthFirst(initNode, traceSeed, forward, orReversed, stepper, top)
            TraceSearch.BFS_BACKWARD ->
              traceProvider.computeBreadthFirst(traceSeed, orReversed, initNode, top)
          }
        // resolve the fired transition (and, for BFS_BACKWARD, the next state) by a forward step
        states.add(layers[0].satOne())
        for (k in 0 until layers.size - 1) {
          val fired =
            forward.withIndex().firstNotNullOfOrNull { (index, transition) ->
              val successors =
                stepper
                  .compute(MddNodePostcondition.of(states[k]), transition, top)
                  .intersection(layers[k + 1])
              if (successors.isTerminalZero) null else index to successors.satOne()
            }
          if (fired != null) {
            actions.add(model.splitAction(fired.first))
            states.add(fired.second)
          } else {
            actions.add(model.action())
            states.add(layers[k + 1].satOne())
          }
        }
      } finally {
        traceProvider.dispose()
        stepper.clear()
        stepper.dispose()
      }

      val valuations =
        states.map {
          PathUtils.extractValuation(
            MddValuationCollector.collect(it).stream().findFirst().orElseThrow(),
            0,
          )
        }
      return@submit Trace.of(valuations.map(ExplState::of), actions)
    }

  val traceTime = Stopwatch.createStarted()
  return try {
    logger.mainStep("Starting trace generation.\n")
    val trace = future.get(traceTimeout, TimeUnit.SECONDS)
    traceTime.stop()
    logger.mainStep("Trace generation finished in ${traceTime.elapsedMillis()}ms.\n")
    trace
  } catch (e: TimeoutException) {
    logger.mainStep("Trace generation timed out.\n")
    future.cancel(true)
    null
  } catch (e: InterruptedException) {
    logger.mainStep("Trace generation interrupted.\n")
    future.cancel(true)
    null
  } catch (e: ExecutionException) {
    throw RuntimeException(e)
  } finally {
    executor.shutdownNow()
  }
}

/**
 * Forward breadth-first layers from [initNode] to a state of [violating], then one backward step
 * per layer: the states of a shortest trace, initial side first.
 */
private fun forwardBreadthFirst(
  initNode: MddHandle,
  violating: MddHandle,
  forward: List<AbstractNextStateDescriptor>,
  orReversed: AbstractNextStateDescriptor,
  stepper: SingleStepProvider,
  top: MddVariableHandle,
): List<MddHandle> {
  val orForward = OrNextStateDescriptor.create(forward)
  val layers = ArrayList<MddHandle>()
  var current = initNode
  var explored = initNode
  layers.add(current)
  var hit = current.intersection(violating)
  while (hit.isTerminalZero) {
    if (Thread.interrupted()) {
      throw InterruptedException("forward search interrupted after ${layers.size} layers")
    }
    val next = stepper.compute(MddNodePostcondition.of(current), orForward, top).minus(explored)
    check(!next.isTerminalZero) { "forward search exhausted the state space without a violation" }
    explored = explored.union(next)
    current = next
    layers.add(current)
    hit = current.intersection(violating)
  }
  val states = arrayOfNulls<MddHandle>(layers.size)
  states[layers.size - 1] = hit.satOne()
  for (j in layers.size - 2 downTo 0) {
    val preds =
      stepper
        .compute(MddNodePostcondition.of(states[j + 1]!!), orReversed, top)
        .intersection(layers[j])
    check(!preds.isTerminalZero) { "no predecessor of the chosen state in the previous layer" }
    states[j] = preds.satOne()
  }
  return states.map { it!! }
}
