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
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExplicitRepresentationExtractor
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SingleStepProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.TraceProvider
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
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
/**
 * A generated trace and the (single) violating state it ends in, in the state order. When
 * [fragmentRefutation] is set the trace does not start at an initial state: the walk was cut short
 * because the concrete suffix it had built was already infeasible, and this is the refutation of
 * that suffix. Such a trace refines but never witnesses a bug.
 */
internal class GeneratedTrace(
  val trace: Trace<ExplState, ExprAction>,
  val target: MddHandle,
  val fragmentRefutation: ItpRefutation? = null,
)

/** How the abstract counterexample is searched between the initial and the violating states. */
enum class TraceSearch {
  /**
   * Backward from the violating states, one arbitrary unexplored predecessor per step with
   * backtracking: cheap steps, but the walk (and so the counterexample) can be far longer than the
   * shortest one and depends on the variable order.
   */
  DFS,
  /**
   * The depth-first walk, cut off by concrete infeasibility: after every few steps the suffix built
   * so far is concretized and checked, and the walk stops as soon as that suffix cannot be
   * concretized. The walk cannot run away, and the refinement instance is the short suffix rather
   * than a whole counterexample, so nothing here needs a shortest path and no breadth-first layer is
   * ever built. Needs the feasibility oracle; without one it behaves like [DFS].
   */
  DFS_FEASIBLE,
  /**
   * Forward breadth-first layers from the initial states until a violating state is reached, then
   * one backward step per layer: the shortest counterexample, with the forward steps on the same
   * (cheap, cached) machinery as saturation.
   */
  BFS,
  /**
   * Backward breadth-first layers from all violating states: also the shortest counterexample, but
   * every layer is a reversed step of a large set, which can cost seconds when many states violate.
   */
  BFS_BACKWARD,
}

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
  search: TraceSearch = TraceSearch.DFS,
  /**
   * Concretizes a suffix and returns the refutation when it is infeasible, null when it still is
   * feasible. Only consulted by [TraceSearch.DFS_FEASIBLE].
   */
  feasibilityOracle: ((Trace<ExplState, ExprAction>) -> ItpRefutation?)? = null,
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
        val forward = explicitTrans.map { MddNodeNextStateDescriptor.of(it) }
        val top = stateSig.topVariableHandle
        if (search == TraceSearch.DFS_FEASIBLE && feasibilityOracle != null) {
          return@submit feasibilityDrivenWalk(
            initNode,
            traceSeed,
            forward,
            orReversed,
            stepper,
            top,
            model,
            feasibilityOracle,
          )
        }
        val layers =
          when (search) {
            TraceSearch.BFS_BACKWARD ->
              traceProvider.computeBreadthFirst(traceSeed, orReversed, initNode, top)
            TraceSearch.BFS ->
              forwardBreadthFirst(initNode, traceSeed, forward, orReversed, stepper, top)
            else -> traceProvider.compute(traceSeed, orReversed, initNode, top)
          }

        // the backward walk records neither the fired transition nor, for the last layer, which
        // violating state is reached: resolve both by stepping forward transition by transition
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

/** How many predecessors the guided walk scores before committing to one. */
private const val PREDECESSOR_SAMPLES = 8

/** The single state's valuation, as the trace states carry it. */
private fun valuationOf(handle: MddHandle) =
  PathUtils.extractValuation(
    MddValuationCollector.collect(handle).stream().findFirst().orElseThrow(),
    0,
  )

/**
 * Depth-first backward walk from [violating], stopped as soon as the concrete suffix it has built is
 * infeasible. One arbitrary unexplored predecessor per step with backtracking, exactly as the plain
 * walk, except that [oracle] is consulted at exponentially spaced lengths; the first infeasible
 * answer ends the search and the suffix is returned as a fragment. Reaching an initial state returns
 * a complete trace as usual.
 */
private fun feasibilityDrivenWalk(
  initNode: MddHandle,
  violating: MddHandle,
  forward: List<AbstractNextStateDescriptor>,
  orReversed: AbstractNextStateDescriptor,
  stepper: SingleStepProvider,
  top: MddVariableHandle,
  model: MonolithicExpr,
  oracle: (Trace<ExplState, ExprAction>) -> ItpRefutation?,
): GeneratedTrace {
  // stack[0] is the violating end; the deepest entry is the one closest to the initial states
  val stack = ArrayList<MddHandle>()
  // actions[j] fires from stack[j + 1] to stack[j]
  val actions = ArrayList<ExprAction>()
  var current = violating.satOne()
  var explored = current
  stack.add(current)
  val target = current
  var nextCheck = 4
  // A blind walk takes an arbitrary predecessor and can wander for thousands of steps before it
  // stumbles into an initial state, which is what made the plain walk unusable. Sample a few
  // predecessors instead and keep the one that agrees with an initial state on the most variables:
  // a cheap greedy pull towards the initial states that needs no distances and no layers.
  val initValuation = valuationOf(initNode.satOne()).toMap()
  fun agreement(handle: MddHandle): Int =
    valuationOf(handle).toMap().count { (decl, value) -> initValuation[decl] == value }

  fun suffixTrace(): Trace<ExplState, ExprAction> =
    Trace.of(
      stack.reversed().map { ExplState.of(valuationOf(it)) },
      actions.reversed().toList(),
    )

  while (current.intersection(initNode).isTerminalZero) {
    if (Thread.interrupted()) {
      throw InterruptedException("feasibility-driven walk interrupted after ${stack.size} steps")
    }
    val preds =
      stepper.compute(MddNodePostcondition.of(current), orReversed, top).minus(explored)
    if (preds.isTerminalZero) {
      // exhausted: give this branch up
      if (stack.size == 1) break
      stack.removeAt(stack.size - 1)
      actions.removeAt(actions.size - 1)
      current = stack[stack.size - 1]
      continue
    }
    var pred = preds.satOne()
    var bestAgreement = agreement(pred)
    var remaining = preds.minus(pred)
    var sampled = 1
    while (sampled < PREDECESSOR_SAMPLES && !remaining.isTerminalZero) {
      val candidate = remaining.satOne()
      val score = agreement(candidate)
      if (score > bestAgreement) {
        bestAgreement = score
        pred = candidate
      }
      remaining = remaining.minus(candidate)
      sampled++
    }
    // which transition fires from the predecessor into the state we came from
    var action: ExprAction = model.action()
    for ((index, transition) in forward.withIndex()) {
      val successors =
        stepper.compute(MddNodePostcondition.of(pred), transition, top).intersection(current)
      if (!successors.isTerminalZero) {
        action = model.splitAction(index)
        break
      }
    }
    explored = explored.union(pred)
    stack.add(pred)
    actions.add(action)
    current = pred

    if (stack.size >= nextCheck) {
      nextCheck *= 2
      val refutation = oracle(suffixTrace())
      if (refutation != null) return GeneratedTrace(suffixTrace(), target, refutation)
    }
  }
  return GeneratedTrace(suffixTrace(), target)
}

/**
 * Forward breadth-first search from [initNode] until a state of [violating] is reached (layers of
 * new states only), then one backward step per layer from that state through [orReversed]: the
 * states of a shortest counterexample, one per layer, initial side first.
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
    check(!next.isTerminalZero) {
      "forward search exhausted the reachable states without reaching a violating state"
    }
    explored = explored.union(next)
    current = next
    layers.add(current)
    hit = current.intersection(violating)
  }
  // one state per layer, chosen backward from the violating state reached
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
