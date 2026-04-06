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
package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.PorLogger
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.model.AtomicFenceLabel.Companion.ATOMIC_MUTEX
import hu.bme.mit.theta.xcfa.model.FenceLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.collectIndirectGlobalVarAccesses
import hu.bme.mit.theta.xcfa.utils.collectIndirectMemoryAccesses
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import java.util.*
import java.util.stream.Collectors
import java.util.stream.Stream
import kotlin.math.max
import kotlin.random.Random
import kotlin.system.measureTimeMillis

/** Wrapper class for actions to redefine equality and hash code based on pid and edge only. */
private class XcfaActionWrapper(val action: XcfaAction) {

  val pid = action.pid
  val edge = action.edge

  override fun toString(): String = "$pid: ${edge.label}"

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is XcfaActionWrapper) return false
    if (pid != other.pid) return false
    if (edge != other.edge) return false
    return true
  }

  override fun hashCode(): Int {
    var result = pid
    result = 31 * result + edge.hashCode()
    return result
  }
}

/** Type definitions for action wrappers and ARG nodes. */
private typealias AW = XcfaActionWrapper

private typealias Node = ArgNode<out S, XcfaAction>

/** Backtrack set of a state: actions to be explored when backtracking in DFS. */
private var State.backtrack: MutableSet<AW> by extension()

/** Sleep set of a state: actions that need not be explored. */
private var State.sleep: MutableSet<AW> by extension()

/** Set of explored actions from a state. */
private var State.explored: MutableSet<AW> by extension()

/** Reexplored actions in a new CEGAR iteration (only relevant when lazy pruning is used). */
private val reExploredDelegate = nullableExtension<State, Boolean?>()
private var State.reExplored: Boolean? by reExploredDelegate

/** Explored actions from an ARG node. */
private val Node.explored: Set<AW>
  get() = outEdges.map { AW(it.action) }.collect(Collectors.toSet())

// for debugging purposes:
var State.number: Int by extension()
var stateNumber = 0

/**
 * An LTS implementing a dynamic partial order reduction algorithm (Source-DPOR) for state space
 * exploration.
 *
 * @see <a href="https://doi.org/10.1145/3073408">Source Sets: A Foundation for Optimal Dynamic
 *   Partial Order Reduction</a>
 */
open class XcfaDporLts(protected open val xcfa: XCFA) : LTS<S, A> {

  companion object {

    var random: Random = Random.Default

    private val dependencySolver: Solver by lazy { Z3SolverFactory.getInstance().createSolver() }

    /** Simple LTS that returns the enabled actions in a state. */
    private val simpleXcfaLts = getXcfaLts()

    /** The enabled actions of a state. */
    private val S.enabled: Collection<AW>
      get() = simpleXcfaLts.getEnabledActionsFor(this).map { AW(it) }

    /** Partial order of states considering sleep sets (unexplored behavior). */
    fun <E : ExprState> getPartialOrder(partialOrd: PartialOrd<E>) =
      PartialOrd<E> { s1, s2 ->
        partialOrd.isLeq(s1, s2) &&
          s2.reExplored == true &&
          s1.sleep.containsAll(s2.sleep - s2.explored)
      }
  }

  /** Represents an element of the DFS search stack. */
  private data class StackItem(
    // the ARG node
    val node: Node,
    // the index of the last actions of processes in the search stack
    val processLastAction: Map<Int, Int> = mutableMapOf(),
    // for each process p it stores the index of the last action of each process that is dependent
    // with the last actions of p
    val lastDependents: Map<Int, Map<Int, Int>> = mutableMapOf(),
    // for each locked mutex the index of the state on the stack where the mutex has been locked
    val mutexLocks: MutableMap<String, Int> = mutableMapOf(),
    private val _backtrack: MutableSet<AW> = mutableSetOf(),
    private val _sleep: MutableSet<AW> = mutableSetOf(),
  ) {

    val action: A
      get() = node.inEdge.get().action // the incoming action to the current state

    val state: S
      get() = node.state // the current state of this stack item

    var backtrack: MutableSet<AW> by node.state::backtrack // backtrack set of the current state

    var sleep: MutableSet<AW> by node.state::sleep // sleep set of the current state
      private set

    var explored: MutableSet<AW> by node.state::explored // explored actions from the current state
      private set

    init {
      backtrack = _backtrack
      sleep = _sleep
      explored = mutableSetOf()
    }

    override fun toString() = action.toString()
  }

  private val spor = XcfaSporLts(xcfa)

  private val stack: Stack<StackItem> = Stack() // the DFS search stack

  private val last
    get() = stack.peek() // the top item of the search stack

  /** Returns an action (wrapped into a set) to be explored from the given state. */
  override fun getEnabledActionsFor(state: S): Set<A> {
    val result: Set<A>
    PorLogger.porTime += measureTimeMillis {
      require(state == last.state)
      val possibleActions = last.backtrack subtract last.sleep
      if (possibleActions.isEmpty()) {
        result = emptySet()
      } else {
        val actionToExplore = possibleActions.random(random)
        last.backtrack.addAll(state.enabled.filter { it.pid == actionToExplore.pid })
        last.sleep.add(actionToExplore)
        last.explored.add(actionToExplore)
        result = setOf(actionToExplore.action)
      }
    }
    return result
  }

  /**
   * A waitlist implementation that controls the search: from which state do we need to explore,
   * pops states from the search stack.
   */
  val waitlist =
    object : Waitlist<Node> {

      /** Adds a new ARG node to the search stack. */
      override fun add(item: Node) {
        PorLogger.porTime += measureTimeMillis {
          var node = item
          // lazy pruning: goes to the root when the stack is empty
          while (stack.isEmpty() && node.parent.isPresent) node = node.parent.get()

          node.state.reExplored =
            true // lazy pruning: indicates that the state is explored in the current iteration
          push(node, stack.size)
        }
      }

      override fun addAll(items: Collection<Node>) {
        require(items.size <= 1)
        if (items.isNotEmpty()) add(items.first())
      }

      override fun addAll(items: Stream<out Node>) {
        val iterator = items.iterator()
        if (iterator.hasNext()) add(iterator.next())
        require(!iterator.hasNext())
      }

      /**
       * Returns true if there is no more actions to explore. States are popped from the stack while
       * there is no more action to be explored.
       */
      override fun isEmpty(): Boolean {
        val result: Boolean
        PorLogger.porTime += measureTimeMillis {
          if (last.node.isCovered && last.node.isFeasible) {
            // if the last node is covered, the subtree of the covering node is explored again (to
            // detect possible races)
            virtualExploration(last.node.coveringNode.get(), stack.size)
          } else {
            // when lazy pruning is used the explored parts from previous iterations are reexplored
            // to
            // detect possible races
            exploreLazily()
          }

          while (
            stack.isNotEmpty() &&
              (last.node.isSubsumed ||
                last.node.isTarget ||
                (last.node.isExpanded && last.backtrack.subtract(last.sleep).isEmpty()))
          ) { // until the last is covered/not feasible, or it has no more action to be explored
            if (stack.size >= 2) {
              val lastButOne = stack[stack.size - 2]

              val neverReleasedMutexes =
                last.mutexLocks.filter { (_, index) -> index == stack.size - 1 }.map { it.key }

              neverReleasedMutexes.forEach { mutex ->
                val blockedActions =
                  lastButOne.state.enabled.filter { action ->
                    mutex == ATOMIC_MUTEX.name ||
                      action.edge.label.getFlatLabels().any {
                        it is FenceLabel && mutex in it.blockingMutexes.map { m -> m.name }
                      }
                  }
                lastButOne.backtrack.addAll(blockedActions)
              }
            }
            stack.pop()
            exploreLazily()
          }
          result = stack.isEmpty()
        }
        return result
      }

      /** Returns the last element of the stack after all unnecessary actions have been removed. */
      override fun remove(): Node {
        if (isEmpty) throw NoSuchElementException("The search stack is empty.")
        return last.node
      }

      override fun size() = stack.size

      /** Clears the search stack and the registry of reexplored actions needed for lazy pruning. */
      override fun clear() {
        stack.clear()
        reExploredDelegate.clear()
      }

      /** Pushes an item to the search stack. */
      private fun push(item: Node, virtualLimit: Int): Boolean {
        item.state.number = stateNumber++ // for debugging purposes
        if (!item.inEdge.isPresent) { // the first item is simply put on the stack
          stack.push(StackItem(item, _backtrack = item.state.enabled.toMutableSet()))
          return true
        }

        val newAction = item.inEdge.get().action
        val process = newAction.pid

        val newProcessLastAction =
          last.processLastAction.toMutableMap().apply { this[process] = stack.size }
        var newLastDependents =
          (last.lastDependents[process]?.toMutableMap() ?: mutableMapOf()).apply {
            this[process] = stack.size
          }
        val relevantProcesses =
          (newProcessLastAction.keys - setOf(process))
            .filter { p -> newLastDependents[p]?.let { it < virtualLimit } ?: true }
            .toMutableSet()

        // Race detection
        for (index in stack.size - 1 downTo 1) {
          if (relevantProcesses.isEmpty()) break
          val node = stack[index].node

          val action = node.inEdge.get().action
          val prevState = node.inEdge.get().source.state
          if (action.pid in relevantProcesses) {
            if (action.pid in newLastDependents && index <= newLastDependents[action.pid]!!) {
              // there is an action a' such that  action -> a' -> newaction  (->: happens-before)
              relevantProcesses.remove(action.pid)
            } else if (dependent(action, newAction) && reversible(prevState, action, newAction)) {
              // reversible race
              val v = notdep(index, newAction)
              val iv = initials(index - 1, v)
              if (iv.isEmpty()) continue // due to mutex (e.g. atomic block)

              if (index < virtualLimit) {
                // only add new action to backtrack sets in the "real" part of the stack
                val backtrack = stack[index - 1].backtrack
                if ((iv intersect backtrack).isEmpty()) {
                  backtrack.add(iv.random(random))
                }
              }

              newLastDependents[action.pid] = index
              newLastDependents = max(newLastDependents, stack[index].lastDependents[action.pid]!!)
              relevantProcesses.remove(action.pid)
            }
          }
        }

        // Set properties of new stack item
        val newProcesses = item.state.processes.keys subtract last.state.processes.keys

        val oldMutexes = last.state.mutexes.keys
        val newMutexes = item.state.mutexes.keys
        val lockedMutexes = newMutexes - oldMutexes
        val releasedMutexes = oldMutexes - newMutexes
        if (!item.state.isBottom) {
          releasedMutexes.forEach { m ->
            last.mutexLocks[m]?.let { stack[it].mutexLocks.remove(m) }
          }
        }

        val isVirtualExploration = virtualLimit < stack.size || item.parent.get() != last.node
        val newSleep =
          if (isVirtualExploration) {
            item.state.sleep
          } else {
            last.sleep.filter { !dependent(it.action, newAction) }.toMutableSet()
          }
        val newBacktrack =
          if (isVirtualExploration) { // for virtual exploration through a covering relation
            item.state.backtrack
          } else {
            val enabledActions = item.state.enabled subtract newSleep
            when {
              item.explored.isNotEmpty() ->
                item.explored.toMutableSet().apply {
                  if (newSleep.containsAll(this) && enabledActions.isNotEmpty()) {
                    this.add(enabledActions.random(random))
                  }
                } // for LAZY pruning

              enabledActions.isNotEmpty() -> {
                val sporSuggestion =
                  sporSuggestion(item.state, enabledActions.map { it.action.pid }).map { AW(it) }
                mutableSetOf((sporSuggestion intersect enabledActions).random(random))
              }

              else -> mutableSetOf()
            }
          }

        // Check cycle before pushing new item on stack
        stack
          .indexOfFirst { it.node == item }
          .let {
            if (it != -1) {
              if (it < virtualLimit) {
                stack[it].backtrack = stack[it].state.enabled.toMutableSet()
              }
              return false
            }
          }

        // Push new item on the stack
        stack.push(
          StackItem(
            node = item,
            processLastAction = newProcessLastAction,
            lastDependents =
              last.lastDependents.toMutableMap().apply {
                this[process] = newLastDependents
                newProcesses.forEach {
                  this[it] = max(this[it] ?: mutableMapOf(), newLastDependents)
                }
              },
            mutexLocks =
              last.mutexLocks.toMutableMap().apply {
                lockedMutexes.forEach { this[it] = stack.size }
                releasedMutexes.forEach(::remove)
              },
            _backtrack = newBacktrack,
            _sleep = newSleep,
          )
        )
        return true
      }

      /** Virtually reexplores part of the ARG for race detection. Used when a node is covered. */
      private fun virtualExploration(node: Node, realStackSize: Int) {
        PorLogger.virtualExplorationTimeMs += measureTimeMillis {
          val startStackSize = stack.size
          val virtualStack = Stack<Node>()
          virtualStack.push(node)
          while (virtualStack.isNotEmpty()) {
            val visiting = virtualStack.pop()
            while (stack.size > startStackSize && stack.peek().node != visiting.parent.get()) {
              stack.pop()
            }

            if (node != visiting) {
              if (!push(visiting, realStackSize) || noInfluenceOnRealExploration(realStackSize))
                continue
            }

            // visiting is not on the stack: no cycle && further virtual exploration can influence
            // real exploration
            if (visiting.isCovered) {
              val coveringNode = visiting.coveringNode.get()
              virtualExploration(coveringNode, realStackSize)
            } else {
              visiting.outEdges.forEach { virtualStack.push(it.target) }
            }
          }
          while (stack.size > startStackSize) stack.pop()
        }
      }

      /** Explores the part of the ARG preserved from previous iterations (see lazy pruning). */
      private fun exploreLazily() {
        while (stack.isNotEmpty()) {
          val lazilyExplorable =
            last.node.outEdges
              .toList()
              .filter { it.target.state.reExplored != true && AW(it.action) !in last.sleep }
              .toSet()
          if (lazilyExplorable.isEmpty()) return

          val edgeToExplore = lazilyExplorable.random(random)
          val actionToExplore = AW(edgeToExplore.action)
          last.backtrack.addAll(last.state.enabled.filter { it.pid == actionToExplore.pid })
          last.sleep.add(actionToExplore)
          last.explored.add(actionToExplore)
          add(edgeToExplore.target)
        }
      }

      /**
       * Returns a map with the keys of the original maps and the maximum of the reference numbers
       * associated to each key.
       */
      private fun max(map1: Map<Int, Int>, map2: Map<Int, Int>) =
        (map1.keys union map2.keys)
          .associateWith { key -> max(map1[key] ?: -1, map2[key] ?: -1) }
          .toMutableMap()

      /** See the article for the definition of notdep. */
      private fun notdep(start: Int, action: A): List<AW> {
        val e = stack[start].action
        return (stack
            .slice(start + 1 until stack.size)
            .filterIndexed { index, item ->
              item.node.parent.get() == stack[start + 1 + index - 1].node &&
                !dependent(e, item.action)
            }
            .map { it.action } + action)
          .map { AW(it) }
      }

      /** See the article for the definition of initials. */
      private fun initials(start: Int, sequence: List<AW>): Set<AW> {
        val state = stack[start].node.state
        return (state.enabled subtract (state.sleep subtract state.explored))
          .filter { enabledAction ->
            for (action in sequence) {
              if (action == enabledAction) {
                return@filter true
              } else if (dependent(enabledAction.action, action.action)) {
                return@filter false
              }
            }
            false
          }
          .toSet()
      }

      /**
       * Returns true when the virtual exploration cannot detect any more races relevant in the
       * "real" exploration (the part of the search stack before the first covering node).
       */
      private fun noInfluenceOnRealExploration(realStackSize: Int) =
        last.processLastAction.keys.all { process ->
          last.lastDependents.containsKey(process) &&
            last.lastDependents[process]!!.all { (_, index) -> index >= realStackSize }
        }
    }

  /** Returns true if a and b are dependent actions. */
  protected fun dependent(a: A, b: A, aSource: S? = null, bSource: S? = null): Boolean {
    val result: Boolean
    PorLogger.dependentTimeMs += measureTimeMillis {
      result =
        dependentControlFlow(a, b) ||
          dependentGlobalVar(a, b) ||
          dependentMemLoc(a, b, aSource, bSource)
    }
    return result
  }

  protected fun dependentControlFlow(a: A, b: A): Boolean = a.pid == b.pid

  protected open fun dependentGlobalVar(a: A, b: A): Boolean {
    val aGlobalVars = a.edge.collectIndirectGlobalVarAccesses(xcfa)
    val bGlobalVars = b.edge.collectIndirectGlobalVarAccesses(xcfa)
    // dependent if they access the same variable (at least one write)
    return (aGlobalVars.keys intersect bGlobalVars.keys).any {
      aGlobalVars[it].isWritten || bGlobalVars[it].isWritten
    }
  }

  protected fun dependentMemLoc(a: A, b: A, aSource: S? = null, bSource: S? = null): Boolean {
    val aMemLocs = a.edge.collectIndirectMemoryAccesses()
    val bMemLocs = b.edge.collectIndirectMemoryAccesses()
    if (aMemLocs.isEmpty() || bMemLocs.isEmpty()) return false

    if (
      (aMemLocs.keys intersect bMemLocs.keys).any {
        aMemLocs[it].isWritten || bMemLocs[it].isWritten
      }
    )
      return true

    val aStateVal =
      (aSource?.sGlobal?.innerState as? ExplState)?.`val` ?: ImmutableValuation.empty()
    val bStateVal =
      (bSource?.sGlobal?.innerState as? ExplState)?.`val` ?: ImmutableValuation.empty()
    val expr: Expr<BoolType> =
      ExprUtils.simplify(
        Or(
          aMemLocs.flatMap { (aMemLoc, aAccess) ->
            bMemLocs.mapNotNull { (bMemLoc, bAccess) ->
              if (aAccess.isWritten || bAccess.isWritten) {
                val aArray = PathUtils.unfold(ExprUtils.simplify(aMemLoc.array, aStateVal), 0)
                val aOffset = PathUtils.unfold(ExprUtils.simplify(aMemLoc.offset, aStateVal), 0)
                val bArray = PathUtils.unfold(ExprUtils.simplify(bMemLoc.array, bStateVal), 1)
                val bOffset = PathUtils.unfold(ExprUtils.simplify(bMemLoc.offset, bStateVal), 1)
                And(Eq(aArray, bArray), Eq(aOffset, bOffset))
              } else null
            }
          }
        )
      )
    if (expr == True()) return true

    return WithPushPop(dependencySolver).use {
      aSource?.let { dependencySolver.add(PathUtils.unfold(it.sGlobal.toExpr(), 0)) }
      bSource?.let { dependencySolver.add(PathUtils.unfold(it.sGlobal.toExpr(), 1)) }
      dependencySolver.add(expr)
      dependencySolver.check().isSat // two pointers may point to the same memory location
    }
  }

  private fun reversible(stateBeforeEarlier: S, earlier: A, latter: A): Boolean =
    latter.label.getFlatLabels().filterIsInstance<FenceLabel>().all { fence ->
      fence.blockingMutexes.none { mutex ->
        stateBeforeEarlier.mutexes[mutex.name]?.contains(earlier.pid) == true
      }
    }

  fun sporSuggestion(state: S, startFromPids: Collection<Int>): Set<A> =
    spor.getEnabledActions(state, startFromPids.toSet())
}

/**
 * Abstraction-aware dynamic partial order reduction (AADPOR) algorithm for state space exploration.
 */
class XcfaAadporLts(xcfa: XCFA) : XcfaDporLts(xcfa) {

  /** The current precision of the abstraction. */
  private lateinit var prec: Prec

  /** Returns actions to be explored from the given state considering the given precision. */
  override fun <P : Prec> getEnabledActionsFor(
    state: S,
    exploredActions: Collection<A>,
    prec: P,
  ): Set<A> {
    this.prec = prec
    return getEnabledActionsFor(state)
  }

  /** Returns true if a and b are dependent actions in the current abstraction. */
  override fun dependentGlobalVar(a: A, b: A): Boolean {
    val precVars = prec.usedVars.toSet()
    val aGlobalVars = a.edge.collectIndirectGlobalVarAccesses(xcfa)
    val bGlobalVars = b.edge.collectIndirectGlobalVarAccesses(xcfa)
    // dependent if they access the same variable in the precision (at least one write)
    return (aGlobalVars.keys intersect bGlobalVars.keys).any {
      (aGlobalVars[it].isWritten || bGlobalVars[it].isWritten) && it.wrappedVar in precVars
    }
  }
}
