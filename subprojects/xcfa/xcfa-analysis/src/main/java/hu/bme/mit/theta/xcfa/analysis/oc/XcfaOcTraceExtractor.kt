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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.util.*

/** Extracts an error trace from the given model. */
internal class XcfaOcTraceExtractor(
  private val xcfa: XCFA,
  private val ocChecker: OcChecker<E>,
  eventGraph: XcfaToEventGraph.EventGraph,
) {

  private val threads: Set<Thread> = eventGraph.threads
  private val events: Map<VarDecl<*>, Map<Int, List<E>>> = eventGraph.events
  private val violations: List<Violation> = eventGraph.violations
  private val pos: List<R> = eventGraph.pos

  internal val trace: Trace<XcfaState<out PtrState<out ExprState>>, XcfaAction>
    get() {
      check(ocChecker.solver.status.isSat)
      val model = ocChecker.solver.model ?: error("No model found for trace extraction.")
      val stateList = mutableListOf<XcfaState<PtrState<ExplState>>>()
      val actionList = mutableListOf<XcfaAction>()
      val valuation = model.toMap()
      val (eventTrace, violation) = getEventTrace(model)

      val processes =
        threads.associate { t ->
          t.pid to
            XcfaProcessState(
              locs = LinkedList(listOf(t.procedure.initLoc)),
              varLookup = LinkedList(listOf()),
            )
        }
      var explState = PtrState(ExplState.of(ImmutableValuation.from(mapOf())))
      stateList.add(XcfaState(xcfa, processes, explState))
      var lastEdge: XcfaEdge = eventTrace[0].edge

      for ((index, event) in eventTrace.withIndex()) {
        valuation[event.const]?.let {
          val newVal =
            explState.innerState.`val`.toMap().toMutableMap().apply { put(event.const.varDecl, it) }
          explState = PtrState(ExplState.of(ImmutableValuation.from(newVal)))
        }

        val nextEdge = eventTrace.getOrNull(index + 1)?.edge
        if (nextEdge != lastEdge) {
          extend(stateList.last(), event.pid, lastEdge.source, explState.innerState)?.let {
            (midActions, midStates) ->
            actionList.addAll(midActions)
            stateList.addAll(midStates)
          }

          val state = stateList.last()
          actionList.add(XcfaAction(event.pid, lastEdge))
          stateList.add(
            state.copy(
              processes =
                state.processes.toMutableMap().apply {
                  put(
                    event.pid,
                    XcfaProcessState(
                      locs = LinkedList(listOf(lastEdge.target)),
                      varLookup = LinkedList(emptyList()),
                    ),
                  )
                },
              sGlobal = explState,
              mutexes = state.mutexes.update(lastEdge, event.pid),
            )
          )
          lastEdge = nextEdge ?: break
        }
      }

      if (!stateList.last().processes[violation.pid]!!.locs.peek().error) {
        extend(stateList.last(), violation.pid, violation.errorLoc, explState.innerState)?.let {
          (midActions, midStates) ->
          actionList.addAll(midActions)
          stateList.addAll(midStates)
        }
      }

      return Trace.of(stateList, actionList)
    }

  private fun getEventTrace(model: Valuation): Pair<List<E>, Violation> {
    val valuation = model.toMap()
    val violation = violations.first { (it.guard.eval(model) as BoolLitExpr).value }

    val relations = ocChecker.getHappensBefore()!!
    val reverseRelations =
      Array(relations.size) { i -> Array(relations.size) { j -> relations[j, i] } }
    val eventsByClk = events.values.flatMap { it.values.flatten() }.groupBy { it.clkId }

    val lastEvents = violation.lastEvents.filter { it.enabled(model) == true }.toMutableList()
    val finished = mutableListOf<E>() // topological order
    while (lastEvents.isNotEmpty()) { // DFS from startEvents as root nodes
      val stack = Stack<StackItem>()
      stack.push(StackItem(lastEvents.removeFirst()))
      while (stack.isNotEmpty()) {
        val top = stack.peek()
        if (top.eventsToVisit == null) {
          val previous =
            reverseRelations[top.event.clkId]
              .flatMapIndexed { i, r -> if (r == null) listOf() else eventsByClk[i] ?: listOf() }
              .filter { it.enabled(model) == true } union
              pos
                .filter {
                  it.to == top.event &&
                    it.enabled(valuation) == true &&
                    it.from.enabled(model) == true
                }
                .map { it.from }
          top.eventsToVisit = previous.toMutableList()
        }

        if (top.eventsToVisit!!.isEmpty()) {
          stack.pop()
          finished.add(top.event)
          continue
        }

        val visiting =
          top.eventsToVisit!!.find { it.clkId == top.event.clkId } ?: top.eventsToVisit!!.first()
        top.eventsToVisit!!.remove(visiting)
        if (visiting !in finished) {
          stack.push(StackItem(visiting))
        }
      }
    }
    return finished to violation
  }

  private fun extend(
    state: XcfaState<PtrState<ExplState>>,
    pid: Int,
    to: XcfaLocation,
    explState: ExplState,
  ): Pair<List<XcfaAction>, List<XcfaState<PtrState<ExplState>>>>? {
    val actions = mutableListOf<XcfaAction>()
    val states = mutableListOf<XcfaState<PtrState<ExplState>>>()
    var currentState = state

    // extend the trace until the target location is reached
    while (
      currentState.mutexes[AtomicFenceLabel.ATOMIC_MUTEX.name]?.equals(pid) == false ||
        currentState.processes[pid]!!.locs.peek() != to
    ) {
      // finish atomic block first
      val stepPid = currentState.mutexes[AtomicFenceLabel.ATOMIC_MUTEX.name]?.first() ?: pid
      val edge =
        currentState.processes[stepPid]!!.locs.peek().outgoingEdges.firstOrNull() ?: return null
      actions.add(XcfaAction(stepPid, edge))
      currentState =
        currentState.copy(
          processes =
            currentState.processes.toMutableMap().apply {
              put(
                stepPid,
                XcfaProcessState(
                  locs = LinkedList(listOf(edge.target)),
                  varLookup = LinkedList(emptyList()),
                ),
              )
            },
          sGlobal = PtrState(explState),
          mutexes = currentState.mutexes.update(edge, stepPid),
        )
      states.add(currentState)
    }
    return actions to states
  }

  private fun Map<String, Set<Int>>.update(edge: XcfaEdge, pid: Int): Map<String, Set<Int>> {
    val map = this.toMutableMap()
    edge.getFlatLabels().forEach {
      if (it is AtomicBeginLabel) map[AtomicFenceLabel.ATOMIC_MUTEX.name] = setOf(pid)
      if (it is AtomicEndLabel) map.remove(AtomicFenceLabel.ATOMIC_MUTEX.name)
    }
    return map
  }
}
