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
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState.Companion.createLookup
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.model.AtomicFenceLabel.Companion.ATOMIC_MUTEX
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.utils.collectVars
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

  // Per-thread renaming of procedure-local variables (params + locals) to thread-instance-specific
  // decls (`T<pid>::_::name`). The event graph already distinguishes thread instances internally
  // (see `threadVar` in XcfaToEventGraph), but the extracted trace is rebuilt from the raw XCFA
  // edges, whose labels carry the bare, instance-agnostic decls. Without this renaming two
  // concurrent instances of the same procedure (e.g. a thread spawned in a loop) would share one
  // local in the linearized trace, so one instance's write clobbers the other's and the sequential
  // re-check in XcfaTraceConcretizer reports a spurious "Infeasible trace". The `T<pid>::_::`
  // prefix
  // matches the convention used by the interleaving analysis and stripped by the witness writer.
  private val pidLookups: Map<Int, Map<VarDecl<*>, VarDecl<*>>> =
    threads.associate { it.pid to it.procedure.createLookup("T${it.pid}") }

  /**
   * Returns [this] edge with its label rewritten to use thread [pid]'s instance-specific local
   * vars.
   */
  private fun XcfaEdge.renamedFor(pid: Int): XcfaEdge {
    val lookup = pidLookups[pid]
    if (lookup.isNullOrEmpty()) return this
    return XcfaEdge(source, target, label.changeVars(lookup), metadata)
  }

  /** The trace to the violation the model of the solver shows. */
  internal val trace: Trace<XcfaState<out PtrState<out ExprState>>, XcfaAction>
    get() {
      val model = model()
      val violation = violations.first { (it.guard.eval(model) as BoolLitExpr).value }
      val lastEvent = violation.lastEvents.first { it.enabled(model) == true }
      return trace(
        model,
        getEventTrace(model, lastEvent.clkId, true),
        violation.pid to violation.errorLoc,
      )
    }

  /**
   * The trace to the state in which the racing accesses [e1] and [e2] (neighbours in the execution
   * the model of the solver shows) are both enabled.
   */
  internal fun raceTrace(e1: E, e2: E): Trace<XcfaState<out PtrState<out ExprState>>, XcfaAction> {
    val model = model()
    val first = if (ocChecker.getHappensBefore()!![e1.clkId, e2.clkId] != null) e1 else e2
    val eventTrace = getEventTrace(model, first.clkId, false)
    // an access in an atomic block goes last: moving it in takes the atomic lock, which moving the
    // other process would first have to release
    val targets = listOf(e1, e2).sortedBy { it.inAtomicBlock }.map { it.pid to it.edge.source }
    return trace(model, eventTrace, *targets.toTypedArray())
  }

  private fun model(): Valuation {
    check(ocChecker.solver.status.isSat)
    return ocChecker.solver.model ?: error("No model found for trace extraction.")
  }

  /** Replays [eventTrace], then moves each process of [targets] on to its target location. */
  private fun trace(
    model: Valuation,
    eventTrace: List<E>,
    vararg targets: Pair<Int, XcfaLocation>,
  ): Trace<XcfaState<out PtrState<out ExprState>>, XcfaAction> {
    val stateList = mutableListOf<XcfaState<PtrState<ExplState>>>()
    val actionList = mutableListOf<XcfaAction>()
    val valuation = model.toMap()
    val processes =
      mapOf(
        0 to
          XcfaProcessState(
            locs = LinkedList(listOf(threads.find { it.pid == 0 }!!.procedure.initLoc)),
            varLookup = noLookup(),
          )
      )
    var explState = PtrState(ExplState.of(ImmutableValuation.from(mapOf())))
    stateList.add(XcfaState(xcfa, processes, explState))
    var lastEdge: XcfaEdge? = eventTrace.firstOrNull()?.edge

    for ((index, event) in eventTrace.withIndex()) {
      val edge = checkNotNull(lastEdge)
      extend(stateList.last(), event.pid, edge.source, explState.innerState)?.let {
        (midActions, midStates) ->
        actionList.addAll(midActions)
        stateList.addAll(midStates)
      }

      valuation[event.const]?.let {
        val newVal =
          explState.innerState.`val`.toMap().toMutableMap().apply { put(event.const.varDecl, it) }
        explState = PtrState(ExplState.of(ImmutableValuation.from(newVal)))
      }

      var state = stateList.last()
      val startedThread = threads.find { it.startEvent == event }
      if (startedThread != null) {
        state =
          state.copy(
            processes =
              state.processes.toMutableMap().apply {
                put(
                  startedThread.pid,
                  XcfaProcessState(
                    locs = LinkedList(listOf(startedThread.procedure.initLoc)),
                    varLookup = noLookup(),
                  ),
                )
              }
          )
      }

      val nextEvent = eventTrace.getOrNull(index + 1)
      val nextEdge = nextEvent?.edge
      if (nextEvent?.pid != event.pid || nextEdge != edge) {
        actionList.add(XcfaAction(event.pid, edge.renamedFor(event.pid)))
        stateList.add(
          state.copy(
            processes =
              state.processes.toMutableMap().apply {
                put(
                  event.pid,
                  XcfaProcessState(locs = LinkedList(listOf(edge.target)), varLookup = noLookup()),
                )
              },
            sGlobal = explState,
            mutexes = state.mutexes.update(edge, event.pid),
          )
        )
        lastEdge = nextEdge ?: break
      }
    }

    for ((pid, loc) in targets) {
      val process = stateList.last().processes[pid] ?: continue
      if (process.locs.peek() == loc) continue
      extend(stateList.last(), pid, loc, explState.innerState)?.let { (midActions, midStates) ->
        actionList.addAll(midActions)
        stateList.addAll(midStates)
      }
    }
    return Trace.of(stateList, actionList)
  }

  /**
   * The enabled events that happen before the atomic unit [startClk] (and those of the unit itself
   * if [includeStart]), in an order consistent with the happens-before relation.
   */
  private fun getEventTrace(model: Valuation, startClk: Int, includeStart: Boolean): List<E> {
    val relations = ocChecker.getHappensBefore()!!
    val reverseRelations =
      Array(relations.size) { i -> Array(relations.size) { j -> relations[j, i] } }
    val eventsByClk = events.values.flatMap { it.values.flatten() }.groupBy { it.clkId }
    val posByClk = pos.filter { it.from.clkId == it.to.clkId }.groupBy { it.from.clkId }

    val finished = mutableListOf<Int>() // topological order
    val stack = Stack<StackItem>()
    stack.push(StackItem(startClk))
    while (stack.isNotEmpty()) {
      val top = stack.peek()
      if (top.eventsToVisit == null) {
        val previous =
          reverseRelations[top.clk].mapIndexedNotNull { i, r -> if (r == null) null else i }
        top.eventsToVisit = previous.toMutableList()
      }

      if (top.eventsToVisit!!.isEmpty()) {
        stack.pop()
        finished.add(top.clk)
        continue
      }

      val visiting = top.eventsToVisit!!.find { it == top.clk - 1 } ?: top.eventsToVisit!!.first()
      top.eventsToVisit!!.remove(visiting)
      if (visiting !in finished) {
        stack.push(StackItem(visiting))
      }
    }

    if (!includeStart) finished.remove(startClk)
    val eventTrace =
      finished.flatMap { clk ->
        val blockPos = posByClk[clk]?.filter { it.enabled(model) }?.toMutableSet() ?: mutableSetOf()
        val deque: Deque<E> = LinkedList()
        val event =
          eventsByClk[clk]?.firstOrNull { it.enabled(model) == true } ?: return@flatMap emptyList()
        deque.add(event)

        while (blockPos.isNotEmpty()) {
          blockPos
            .find { it.to == deque.first }
            ?.let {
              blockPos.remove(it)
              deque.addFirst(it.from)
            }
            ?: blockPos
              .find { it.from == deque.last }
              ?.let {
                blockPos.remove(it)
                deque.addLast(it.to)
              }
            ?: break
        }

        deque
      }

    return eventTrace
  }

  private data class StackItem(val clk: Int) {

    var eventsToVisit: MutableList<Int>? = null
  }

  private fun R.enabled(model: Valuation): Boolean =
    from.enabled(model) == true && to.enabled(model) == true

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
      currentState.processes[pid]!!.locs.peek() != to ||
        (currentState.mutexes[ATOMIC_MUTEX.name]?.first() ?: pid) != pid
    ) {
      // finish atomic block first
      val stepPid = currentState.mutexes[ATOMIC_MUTEX.name]?.first() ?: pid
      val edge =
        currentState.processes[stepPid]!!.locs.peek().outgoingEdges.firstOrNull() ?: return null
      check(stepPid == pid || edge.label.collectVars().isEmpty()) {
        "Atomic mutex is held by another thread which still has events in its atomic block."
      }
      actions.add(XcfaAction(stepPid, edge.renamedFor(stepPid)))
      currentState =
        currentState.copy(
          processes =
            currentState.processes.toMutableMap().apply {
              put(
                stepPid,
                XcfaProcessState(locs = LinkedList(listOf(edge.target)), varLookup = noLookup()),
              )
            },
          sGlobal = PtrState(explState),
          mutexes = currentState.mutexes.update(edge, stepPid),
        )
      states.add(currentState)
    }
    return actions to states
  }

  /** One empty frame: the labels are already instance-specific, but a frame has to be present. */
  private fun noLookup() = LinkedList(listOf(mapOf<VarDecl<*>, VarDecl<*>>()))

  private fun Map<String, Set<Int>>.update(edge: XcfaEdge, pid: Int): Map<String, Set<Int>> {
    val map = this.toMutableMap()
    edge.getFlatLabels().forEach {
      if (it is AtomicBeginLabel) map[ATOMIC_MUTEX.name] = setOf(pid)
      if (it is AtomicEndLabel) map.remove(ATOMIC_MUTEX.name)
    }
    return map
  }
}
