/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.isWritten
import hu.bme.mit.theta.xcfa.model.XCFA
import java.util.*
import java.util.stream.Collectors
import java.util.stream.Stream
import kotlin.math.max
import kotlin.random.Random

/**
 * Type definitions for states, actions and ARG nodes.
 */
private typealias S = XcfaState<out ExprState>
private typealias A = XcfaAction
private typealias Node = ArgNode<out S, A>

/**
 * Backtrack set of a state: actions to be explored when backtracking in DFS.
 */
private var State.backtrack: MutableSet<A> by extension()

/**
 * Sleep set of a state: actions that need not be explored.
 */
private var State.sleep: MutableSet<A> by extension()

/**
 * Set of explored actions from a state.
 */
private var State.explored: MutableSet<A> by extension()

/**
 * Reexplored actions in a new CEGAR iteration (only relevant when lazy pruning is used).
 */
private val reExploredDelegate = nullableExtension<State, Boolean?>()
private var State.reExplored: Boolean? by reExploredDelegate

/**
 * Explored actions from an ARG node.
 */
private val Node.explored: Set<A> get() = outEdges.map { it.action }.collect(Collectors.toSet())

/**
 * An LTS implementing a dynamic partial order reduction algorithm (Source-DPOR) for state space exploration.
 * @see <a href="https://doi.org/10.1145/3073408">Source Sets: A Foundation for Optimal Dynamic Partial Order Reduction</a>
 */
open class XcfaDporLts(private val xcfa: XCFA) : LTS<S, A> {

    companion object {

        var random: Random =
            Random.Default // use Random(seed) with a seed or Random.Default without seed

        /**
         * Simple LTS that returns the enabled actions in a state.
         */
        private val simpleXcfaLts = getXcfaLts()

        /**
         * The enabled actions of a state.
         */
        private val State.enabled: Collection<A>
            get() = simpleXcfaLts.getEnabledActionsFor(this as S)

        /**
         * Partial order of states considering sleep sets (unexplored behavior).
         */
        fun <E : ExprState> getPartialOrder(partialOrd: PartialOrd<E>) = PartialOrd<E> { s1, s2 ->
            partialOrd.isLeq(
                s1, s2
            ) && s2.reExplored == true && s1.sleep.containsAll(s2.sleep - s2.explored)
        }
    }

    /**
     * Represents an element of the DFS search stack.
     */
    private data class StackItem(
        val node: Node, // the ARG node
        val processLastAction: Map<Int, Int> = mutableMapOf(), // the index of the last actions of processes in the search stack
        val lastDependents: Map<Int, Map<Int, Int>> = mutableMapOf(), // for each process p it stores the index of the last action of each process that is dependent with the last actions of p
        val mutexLocks: MutableMap<String, Int> = mutableMapOf(), // for each locked mutex the index of the state on the stack where the mutex has been locked
        private val _backtrack: MutableSet<A> = mutableSetOf(),
        private val _sleep: MutableSet<A> = mutableSetOf(),
    ) {

        val action: A get() = node.inEdge.get().action // the incoming action to the current state

        val state: S get() = node.state // the current state of this stack item

        var backtrack: MutableSet<A> by node.state::backtrack // backtrack set of the current state

        var sleep: MutableSet<A> by node.state::sleep // sleep set of the current state
            private set

        var explored: MutableSet<A> by node.state::explored // explored actions from the current state
            private set

        init {
            backtrack = _backtrack
            sleep = _sleep
            explored = mutableSetOf()
        }

        override fun toString() = action.toString()
    }

    private val stack: Stack<StackItem> = Stack() // the DFS search stack

    private val last get() = stack.peek() // the top item of the search stack

    /**
     * Returns an action (wrapped into a set) to be explored from the given state.
     */
    override fun getEnabledActionsFor(state: S): Set<A> {
        require(state == last.state)
        val possibleActions = last.backtrack subtract last.sleep
        if (possibleActions.isEmpty()) return emptySet()

        val actionToExplore = possibleActions.random(random)
        last.backtrack.addAll(state.enabled.filter { it.pid == actionToExplore.pid })
        last.sleep.add(actionToExplore)
        last.explored.add(actionToExplore)
        return setOf(actionToExplore)
    }

    /**
     * A waitlist implementation that controls the search: from which state do we need to explore, pops states from the search stack.
     */
    val waitlist = object : Waitlist<Node> {

        /**
         * Adds a new ARG node to the search stack.
         */
        override fun add(item: Node) {
            var node = item
            // lazy pruning: goes to the root when the stack is empty
            while (stack.isEmpty() && node.parent.isPresent) node = node.parent.get()

            node.state.reExplored =
                true // lazy pruning: indicates that the state is explored in the current iteration
            push(node, stack.size)
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
         * Returns true if there is no more actions to explore. States are popped from the stack while there is no more action to be explored.
         */
        override fun isEmpty(): Boolean {
            if (last.node.isCovered && last.node.isFeasible) {
                // if the last node is covered, the subtree of the covering node is explored again (to detect possible races)
                virtualExploration(last.node.coveringNode.get(), stack.size)
            } else {
                // when lazy pruning is used the explored parts from previous iterations are reexplored to detect possible races
                exploreLazily()
            }
            while (stack.isNotEmpty() && (last.node.isSubsumed || (last.node.isExpanded && last.backtrack.subtract(
                    last.sleep
                ).isEmpty()))
            ) { // until we need to pop (the last is covered or not feasible, or it has no more actions that need to be explored
                if (stack.size >= 2) {
                    val lastButOne = stack[stack.size - 2]
                    val mutexNeverReleased =
                        last.mutexLocks.containsKey(
                            "") && (last.state.mutexes.keys subtract lastButOne.state.mutexes.keys).contains(
                            ""
                        )
                    if (last.node.explored.isEmpty() || mutexNeverReleased) {
                        // if a mutex is never released another action (practically all the others) have to be explored
                        lastButOne.backtrack = lastButOne.state.enabled.toMutableSet()
                    }
                }
                stack.pop()
                exploreLazily()
            }
            return stack.isEmpty()
        }

        /**
         * Returns the last element of the stack after all unnecessary actions have been removed.
         */
        override fun remove(): Node {
            if (isEmpty) throw NoSuchElementException("The search stack is empty.")
            return last.node
        }

        override fun size() = stack.size

        /**
         * Clears the search stack and the registry of reexplored actions needed for lazy pruning.
         */
        override fun clear() {
            stack.clear()
            reExploredDelegate.clear()
        }

        /**
         * Pushes an item to the search stack.
         */
        private fun push(item: Node, virtualLimit: Int): Boolean {
            if (!item.inEdge.isPresent) { // the first item is simply put on the stack
                stack.push(StackItem(item, _backtrack = item.state.enabled.toMutableSet()))
                return true
            }

            val newaction = item.inEdge.get().action
            val process = newaction.pid

            val newProcessLastAction =
                last.processLastAction.toMutableMap().apply { this[process] = stack.size }
            var newLastDependents =
                (last.lastDependents[process]?.toMutableMap() ?: mutableMapOf()).apply {
                    this[process] = stack.size
                }
            val relevantProcesses = (newProcessLastAction.keys - setOf(process)).toMutableSet()

            // Race detection
            for (index in stack.size - 1 downTo 1) {
                if (relevantProcesses.isEmpty()) break
                val node = stack[index].node

                val action = node.inEdge.get().action
                if (relevantProcesses.contains(action.pid)) {
                    if (newLastDependents.containsKey(action.pid) && index <= checkNotNull(
                            newLastDependents[action.pid])) {
                        // there is an action a' such that  action -> a' -> newaction  (->: happens-before)
                        relevantProcesses.remove(action.pid)
                    } else if (dependent(newaction, action)) {
                        // reversible race
                        val v = notdep(index, newaction)
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
                        newLastDependents =
                            max(newLastDependents, checkNotNull(stack[index].lastDependents[action.pid]))
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
                    last.mutexLocks[m]?.let {
                        stack[it].mutexLocks.remove(
                            m
                        )
                    }
                }
            }

            val isVirtualExploration = virtualLimit < stack.size || item.parent.get() != last.node
            val newSleep = if (isVirtualExploration) {
                item.state.sleep
            } else {
                last.sleep.filter { !dependent(it, newaction) }.toMutableSet()
            }
            val enabledActions = item.state.enabled subtract newSleep
            val newBacktrack = when {
                isVirtualExploration -> item.state.backtrack // for virtual exploration through a covering relation
                item.explored.isNotEmpty() -> item.explored.toMutableSet().apply {
                    if (newSleep.containsAll(this) && enabledActions.isNotEmpty()) {
                        this.add(enabledActions.random(random))
                    }
                } // for LAZY pruning
                enabledActions.isNotEmpty() -> mutableSetOf(enabledActions.random(random))
                else -> mutableSetOf()
            }

            // Check cycle before pushing new item on stack
            stack.indexOfFirst { it.node == item }.let {
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
                    lastDependents = last.lastDependents.toMutableMap().apply {
                        this[process] = newLastDependents
                        newProcesses.forEach {
                            this[it] = max(this[it] ?: mutableMapOf(), newLastDependents)
                        }
                    },
                    mutexLocks = last.mutexLocks.toMutableMap().apply {
                        lockedMutexes.forEach { this[it] = stack.size }
                        releasedMutexes.forEach(::remove)
                    },
                    _backtrack = newBacktrack,
                    _sleep = newSleep,
                )
            )
            return true
        }

        /**
         * Virtually reexplores part of the ARG for race detection. Used when a node is covered.
         */
        private fun virtualExploration(node: Node, realStackSize: Int) {
            val startStackSize = stack.size
            val virtualStack = Stack<Node>()
            virtualStack.push(node)
            while (virtualStack.isNotEmpty()) {
                val visiting = virtualStack.pop()
                while (stack.size > startStackSize && stack.peek().node != visiting.parent.get()) stack.pop()

                if (node != visiting) {
                    if (!push(visiting, startStackSize) || noInfluenceOnRealExploration(
                            realStackSize
                        )
                    ) continue
                }

                // visiting is not on the stack: no cycle && further virtual exploration can influence real exploration
                if (visiting.isCovered) {
                    val coveringNode = visiting.coveringNode.get()
                    virtualExploration(coveringNode, realStackSize)
                } else {
                    visiting.outEdges.forEach { virtualStack.push(it.target) }
                }
            }
            while (stack.size > startStackSize) stack.pop()
        }

        /**
         * Explores the part of the ARG preserved from previous iterations (see lazy pruning).
         */
        private fun exploreLazily() {
            while (stack.isNotEmpty()) {
                val lazilyExplorable = last.node.outEdges.toList()
                    .filter { it.target.state.reExplored != true && it.action !in last.sleep }
                    .toSet()
                if (lazilyExplorable.isEmpty()) return

                val edgeToExplore = lazilyExplorable.random(random)
                val actionToExplore = edgeToExplore.action
                last.backtrack.addAll(last.state.enabled.filter { it.pid == actionToExplore.pid })
                last.sleep.add(actionToExplore)
                last.explored.add(actionToExplore)
                add(edgeToExplore.target)
            }
        }

        /**
         * Returns a map with the keys of the original maps and the maximum of the reference numbers associated to each key.
         */
        private fun max(map1: Map<Int, Int>, map2: Map<Int, Int>) =
            (map1.keys union map2.keys).associateWith { key ->
                max(
                    map1[key] ?: -1, map2[key] ?: -1
                )
            }.toMutableMap()

        /**
         * See the article for the definition of notdep.
         */
        private fun notdep(start: Int, action: A): List<A> {
            val e = stack[start].action
            return stack.slice(start + 1 until stack.size).filterIndexed { index, item ->
                item.node.parent.get() == stack[start + 1 + index - 1].node && !dependent(
                    e, item.action
                )
            }.map { it.action }.toMutableList().apply { add(action) }
        }

        /**
         * See the article for the definition of initials.
         */
        private fun initials(start: Int, sequence: List<A>): Set<A> {
            val state = stack[start].node.state
            return (state.enabled subtract (state.sleep subtract state.explored)).filter { enabledAction ->
                for (action in sequence) {
                    if (action == enabledAction) {
                        return@filter true
                    } else if (dependent(enabledAction, action)) {
                        return@filter false
                    }
                }
                false
            }.toSet()
        }

        /**
         * Returns true when the virtual exploration cannot detect any more races relevant in the "real" exploration (the part of the search stack before the first covering node).
         */
        private fun noInfluenceOnRealExploration(realStackSize: Int) =
            last.processLastAction.keys.all { process ->
                last.lastDependents.containsKey(process) &&
                    checkNotNull(last.lastDependents[process]).all { (_, index) ->
                        index >= realStackSize
                    }
            }
    }

    /**
     * Returns true if a and b are dependent actions.
     */
    protected open fun dependent(a: A, b: A): Boolean {
        if (a.pid == b.pid) return true

        val aGlobalVars = a.edge.getGlobalVars(xcfa)
        val bGlobalVars = b.edge.getGlobalVars(xcfa)
        // dependent if they access the same variable (at least one write)
        return (aGlobalVars.keys intersect bGlobalVars.keys).any { aGlobalVars[it].isWritten || bGlobalVars[it].isWritten }
    }
}

/**
 * Abstraction-aware dynamic partial order reduction (AADPOR) algorithm for state space exploration.
 */
class XcfaAadporLts(private val xcfa: XCFA) : XcfaDporLts(xcfa) {

    /**
     * The current precision of the abstraction.
     */
    private lateinit var prec: Prec

    /**
     * Returns actions to be explored from the given state considering the given precision.
     */
    override fun <P : Prec> getEnabledActionsFor(state: S, exploredActions: Collection<A>, prec: P): Set<A> {
        this.prec = prec
        return getEnabledActionsFor(state)
    }

    /**
     * Returns true if a and b are dependent actions in the current abstraction.
     */
    override fun dependent(a: A, b: A): Boolean {
        if (a.pid == b.pid) return true

        val aGlobalVars = a.edge.getGlobalVars(xcfa)
        val bGlobalVars = b.edge.getGlobalVars(xcfa)
        val precVars = prec.usedVars.toSet()
        // dependent if they access the same variable in the precision (at least one write)
        return (aGlobalVars.keys intersect bGlobalVars.keys intersect precVars).any { aGlobalVars[it].isWritten || bGlobalVars[it].isWritten }
    }
}
