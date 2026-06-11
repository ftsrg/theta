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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddSignature
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.ReverseNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExplicitRepresentationExtractor
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
 * Backward trace generation shared by [MddChecker] and [MddCegarChecker]: reverses the transition
 * nodes over the computed state space and walks from [propViolating] back to [initNode]. Returns
 * null if generation does not finish within [traceTimeout] seconds.
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
): Trace<ExplState, ExprAction>? {
  // when an initial state itself violates, seed with the initial violating states: TraceProvider
  // would accept the whole violating set as a length-1 trace and the valuation collector could
  // pick a non-initial state from it, producing a trace that fails concretization
  val initViolating = propViolating.intersection(initNode) as MddHandle
  val traceSeed =
    if (MddInterpreter.calculateNonzeroCount(initViolating) > 0) initViolating else propViolating

  val executor = Executors.newSingleThreadExecutor()
  val future =
    executor.submit<Trace<ExplState, ExprAction>> {
      val reversedDescriptors = mutableListOf<AbstractNextStateDescriptor>()
      for (transNode in transNodes) {
        val explTrans =
          MddExplicitRepresentationExtractor.transform(transNode, transSig.topVariableHandle)
        reversedDescriptors.add(ReverseNextStateDescriptor.of(stateSpace, explTrans))
      }
      val orReversed = OrNextStateDescriptor.create(reversedDescriptors)

      val traceProvider = TraceProvider(stateSig.variableOrder)
      val mddTrace =
        traceProvider.compute(traceSeed, orReversed, initNode, stateSig.topVariableHandle)
      val valuations =
        mddTrace
          .map {
            PathUtils.extractValuation(
              MddValuationCollector.collect(it).stream().findFirst().orElseThrow(),
              0,
            )
          }
          .toList()
      return@submit Trace.of(valuations.map(ExplState::of), model.action())
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
