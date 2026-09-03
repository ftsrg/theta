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
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SingleStepProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.TraceProvider
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
 * Backward trace generation shared by [hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker] and
 * [hu.bme.mit.theta.analysis.algorithm.mdd.cegar.MddCegarChecker]: reverses the transition nodes
 * over the computed state space and walks from [propViolating] back to [initNode]. Returns null if
 * generation does not finish within [traceTimeout] seconds. With seeding the trans order has concrete
 * witness levels below the abstract ones that [stateSig] lacks, so [transDataBoundary] must cut the
 * extraction there — otherwise the reversed descent outlives the state recursion.
 *
 * Each step of the returned trace carries the action of the transition (element of
 * [MonolithicExpr.split], matched by index to [transNodes]) that produced it, resolved by a forward
 * step from the previous state; the final state is chosen as a successor of its predecessor inside the
 * violating set, not an arbitrary violating state.
 */
/** A generated trace and the (single) violating state it ends in, in the state order. */
internal class GeneratedTrace(val trace: Trace<ExplState, ExprAction>, val target: MddHandle)

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
  transDataBoundary: Any? = null,
  /** Violating states not to end in (targets of traces generated earlier in the same iteration). */
  excluded: MddHandle? = null,
  /** Breadth-first backward search (shortest counterexample) instead of the depth-first walk. */
  breadthFirst: Boolean = false,
): GeneratedTrace? {
  val violating = if (excluded != null) propViolating.minus(excluded) else propViolating
  if (violating.isTerminalZero) return null
  // when an initial state itself violates, seed with the initial violating states: TraceProvider
  // would accept the whole violating set as a length-1 trace and the valuation collector could
  // pick a non-initial state from it, producing a trace that fails concretization
  val initViolating = violating.intersection(initNode)
  val traceSeed =
    if (MddInterpreter.calculateNonzeroCount(initViolating) > 0) initViolating else violating

  val executor = Executors.newSingleThreadExecutor()
  val future =
    executor.submit<GeneratedTrace> {
      val mirrorTop = MddExplicitRepresentationExtractor.mirrorTopOf(transSig.topVariableHandle)
      val explicitTrans =
        transNodes.map {
          MddExplicitRepresentationExtractor.transform(it, mirrorTop, transDataBoundary)
        }
      val reversedDescriptors: List<AbstractNextStateDescriptor> =
        explicitTrans.map { ReverseNextStateDescriptor.of(stateSpace, it) }
      val orReversed = OrNextStateDescriptor.create(reversedDescriptors)

      // both providers register themselves on the graph: dispose them, or every iteration's trace
      // caches (reversed relations, single-step results) stay reachable for the whole run
      val traceProvider = TraceProvider(stateSig.variableOrder)
      val stepper = SingleStepProvider(stateSig.variableOrder)
      val states = ArrayList<MddHandle>()
      val actions = ArrayList<ExprAction>()
      try {
        val layers =
          if (breadthFirst)
            traceProvider.computeBreadthFirst(
              traceSeed,
              orReversed,
              initNode,
              stateSig.topVariableHandle,
            )
          else traceProvider.compute(traceSeed, orReversed, initNode, stateSig.topVariableHandle)

        // the backward walk records neither the fired transition nor, for the last layer, which
        // violating state is reached: resolve both by stepping forward transition by transition
        val forward = explicitTrans.map { MddNodeNextStateDescriptor.of(it) }
        val top = stateSig.topVariableHandle
        states.add(layers[0].satOne())
        for (k in 0 until layers.size - 1) {
          val source = states[k]
          var resolved = false
          for ((index, transition) in forward.withIndex()) {
            val successors =
              stepper
                .compute(MddNodePostcondition.of(source), transition, top)
                .intersection(layers[k + 1])
            if (!successors.isTerminalZero) {
              states.add(successors.satOne())
              actions.add(model.splitAction(index))
              resolved = true
              break
            }
          }
          if (!resolved) {
            // should not happen: fall back to the layer's own state and the whole relation
            states.add(layers[k + 1].satOne())
            actions.add(model.action())
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
      return@submit GeneratedTrace(Trace.of(valuations.map(ExplState::of), actions), states.last())
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
