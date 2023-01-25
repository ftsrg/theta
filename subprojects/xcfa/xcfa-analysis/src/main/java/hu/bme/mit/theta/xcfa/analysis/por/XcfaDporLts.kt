package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import java.util.stream.Collectors
import java.util.stream.Stream
import kotlin.math.max
import kotlin.properties.ReadWriteProperty
import kotlin.random.Random
import kotlin.reflect.KProperty

private typealias S = XcfaState<out ExprState>
private typealias A = XcfaAction
private typealias Node = ArgNode<out S, A>

private class ExtensionProperty<R, T> : ReadWriteProperty<R, T> {
    val map = mutableMapOf<R, T>()
    override fun getValue(thisRef: R, property: KProperty<*>) = map[thisRef]!!
    override fun setValue(thisRef: R, property: KProperty<*>, value: T) {
        map[thisRef] = value
    }
}

private class NullableExtensionProperty<R, T> : ReadWriteProperty<R, T?> {
    val map = mutableMapOf<R, T?>()
    override fun getValue(thisRef: R, property: KProperty<*>) = map[thisRef]
    override fun setValue(thisRef: R, property: KProperty<*>, value: T?) {
        map[thisRef] = value
    }
}

private fun <R, T> extension() = ExtensionProperty<R, T>()
private fun <R, T> nullableExtension() = NullableExtensionProperty<R, T?>()

// DEBUG
var State.reachedNumber: Int? by nullableExtension()
// GUBED

var State.backtrack: MutableSet<A> by extension() // TODO private
var State.sleep: MutableSet<A> by extension() // TODO private

val Node.explored: Set<A> get() = outEdges.map { it.action }.collect(Collectors.toSet())

/**
 * Dynamic partial order reduction algorithm for state space exploration.
 * @see <a href="https://doi.org/10.1145/3073408">Source Sets: A Foundation for Optimal Dynamic Partial Order Reduction</a>
 */
class XcfaDporLts(private val xcfa: XCFA) : LTS<S, A> {

    init {
        System.err.println(xcfa.toDot())
    }

    companion object {
        var random: Random = Random.Default // use Random(seed) with a seed or Random.Default without seed

        fun <E : ExprState> getPartialOrder(partialOrd: PartialOrd<E>) =
            PartialOrd<E> { s1, s2 -> partialOrd.isLeq(s1, s2) && s1.sleep.containsAll(s2.sleep) }
    }

    private data class StackItem(
        val node: Node,
        val processLastAction: Map<Int, Int> = mutableMapOf(),
        val lastDependents: Map<Int, Map<Int, Int>> = mutableMapOf(),
        val mutexLocks: MutableMap<String, Int> = mutableMapOf(),
        private val _backtrack: MutableSet<A> = mutableSetOf(),
        private val _sleep: MutableSet<A> = mutableSetOf(),
    ) {
        val action: A get() = node.inEdge.get().action
        val state: S get() = node.state
        var backtrack: MutableSet<A> by node.state::backtrack
        var sleep: MutableSet<A> by node.state::sleep
            private set

        init {
            backtrack = _backtrack
            sleep = _sleep
        }

        override fun toString() = action.toString()
    }

    private val simpleXcfaLts = getXcfaLts()

    private val stack: Stack<StackItem> = Stack()

    private val last get() = stack.peek()

    private fun getAllEnabledActionsFor(state: S): Set<A> = simpleXcfaLts.getEnabledActionsFor(state)

    override fun getEnabledActionsFor(state: S): Set<A> {
        require(state == last.state)
        val possibleActions = last.backtrack subtract last.sleep
        if (possibleActions.isEmpty()) return emptySet()

        val actionToExplore = possibleActions.random()
        val enabledActions = getAllEnabledActionsFor(state)
        last.backtrack.addAll(enabledActions.filter { it.pid == actionToExplore.pid })
        last.sleep.add(actionToExplore)
        return setOf(actionToExplore)
    }

    val waitlist = object : Waitlist<Node> {

        var counter = 0

        private fun max(map1: Map<Int, Int>, map2: Map<Int, Int>) =
            (map1.keys union map2.keys).associateWith { key -> max(map1[key] ?: -1, map2[key] ?: -1) }.toMutableMap()

        override fun add(item: Node) {
            item.state.reachedNumber = counter++
            push(item, stack.size)

            // DEBUG
            if (stack.size >= 2) {
                val stackItem = stack[stack.size - 2]
                stackItem.state.backtrack = stackItem.backtrack
                stackItem.state.sleep = stackItem.sleep
            }
            // GUBED
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

        override fun isEmpty(): Boolean {
            if (last.node.isCovered && last.node.isFeasible) {
                virtualExploration(last.node.coveringNode.get(), stack.size)
            }
            while (stack.isNotEmpty() &&
                (last.node.isSubsumed || (last.node.isExpanded && last.backtrack.subtract(last.sleep).isEmpty()))
            ) {
                if (stack.size >= 2) {
                    val lastButOne = stack[stack.size - 2]
                    val mutexNeverReleased = last.mutexLocks.containsKey("") &&
                            (last.state.mutexes.keys subtract lastButOne.state.mutexes.keys).contains("")
                    if (last.node.explored.isEmpty() || mutexNeverReleased) {
                        lastButOne.backtrack = getAllEnabledActionsFor(lastButOne.state).toMutableSet()
                    }
                }
                stack.pop()
            }
            return stack.isEmpty()
        }

        override fun remove(): Node {
            if (isEmpty) throw NoSuchElementException("The search stack is empty.")
            return last.node
        }

        override fun size() = stack.count { it.backtrack.isNotEmpty() }

        override fun clear() = stack.clear()

        private fun push(item: Node, virtualLimit: Int): Boolean {
            if (!item.inEdge.isPresent) {
                stack.push(StackItem(item, _backtrack = getAllEnabledActionsFor(item.state).toMutableSet()))
                return true
            }

            val newaction = item.inEdge.get().action
            val process = newaction.pid
            val newProcessLastAction = LinkedHashMap(last.processLastAction).apply { this[process] = stack.size }
            var newLastDependents: MutableMap<Int, Int> = LinkedHashMap(last.lastDependents[process] ?: mapOf()).apply {
                this[process] = stack.size
            }
            val relevantProcesses = (newProcessLastAction.keys - setOf(process)).toMutableSet()

            // Race detection
            for (index in stack.size - 1 downTo 1) {
                if (relevantProcesses.isEmpty()) break
                val node = stack[index].node
                val action = node.inEdge.get().action
                if (relevantProcesses.contains(action.pid)) {
                    if (newLastDependents.containsKey(action.pid) && index <= newLastDependents[action.pid]!!) {
                        // there is an action a' such that  action -> a' -> newaction  (->: happens-before)
                        relevantProcesses.remove(action.pid)
                    } else if (dependent(newaction, action)) {
                        // reversible race
                        if (index < virtualLimit) {
                            val v = notdep(index, newaction)
                            val iv = initials(index - 1, v)
                            if (iv.isEmpty()) continue // due to mutex (e.g. atomic block)

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
            releasedMutexes.forEach { m -> last.mutexLocks[m]?.let { stack[it].mutexLocks.remove(m) } }

            val newSleep = last.sleep.filter { !dependent(it, newaction) }.toMutableSet()
            val enabledActions = getAllEnabledActionsFor(item.state) subtract newSleep
            val enabledProcesses = enabledActions.map { it.pid }.toSet()

            // Check cycle before pushing new item on stack
            stack.find { it.node == item }?.let { // a cycle in the state space
                it.backtrack = getAllEnabledActionsFor(it.state).toMutableSet()
                return false
            }

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
                    mutexLocks = last.mutexLocks.apply {
                        lockedMutexes.forEach { this[it] = stack.size }
                        releasedMutexes.forEach(::remove)
                    },
                    _backtrack = if (enabledProcesses.isEmpty()) {
                        mutableSetOf()
                    } else {
                        mutableSetOf(enabledActions.random(random))
                    },
                    _sleep = newSleep,
                )
            )
            return true
        }

        private fun virtualExploration(node: Node, realStackSize: Int) {
            val startStackSize = stack.size
            val virtualStack = Stack<Node>()
            virtualStack.push(node)
            while (virtualStack.isNotEmpty()) {
                val visiting = virtualStack.pop()
                while (stack.size > startStackSize && stack.peek().node != visiting.parent.get()) stack.pop()

                if (push(visiting, startStackSize) && !noInfluenceOnRealExploration(realStackSize)) {
                    // visiting is not on the stack: no cycle && further virtual exploration can influence real exploration
                    if (visiting.isCovered) {
                        val coveringNode = visiting.coveringNode.get()
                        virtualExploration(coveringNode, realStackSize)
                    } else {
                        visiting.outEdges.forEach { virtualStack.push(it.target) }
                    }
                }
            }
            while (stack.size > startStackSize) stack.pop()
        }

        private fun dependent(a: A, b: A): Boolean {
            if (a.pid == b.pid) return true

            // TODO caching...
            val aGlobalVars = a.edge.getGlobalVars(xcfa)
            val bGlobalVars = b.edge.getGlobalVars(xcfa)
            if ((aGlobalVars.keys intersect bGlobalVars.keys).any { aGlobalVars[it] == true || bGlobalVars[it] == true }) {
                // they access the same variable (at least one write)
                return true
            }
            return false
        }

        private fun notdep(start: Int, action: A): List<A> {
            val e = stack[start].action
            return stack.slice(start + 1 until stack.size)
                .map { it.action }
                .filter { !dependent(e, it) }
                .toMutableList().apply { add(action) }
        }

        private fun initials(start: Int, sequence: List<A>): Set<A> {
            return getAllEnabledActionsFor(stack[start].node.state).filter { enabledAction ->
                for (action in sequence) {
                    if (action == enabledAction) {
                        return@filter true
                    } else if (dependent(enabledAction, action)) {
                        return@filter false
                    }
                }
                true
            }.toSet()
        }

        private fun noInfluenceOnRealExploration(realStackSize: Int) = last.processLastAction.keys.all { process ->
            last.lastDependents.containsKey(process) && last.lastDependents[process]!!.all { (otherProcess, index) ->
                index >= realStackSize || index >= last.processLastAction[otherProcess]!!
            }
        }
    }
}
