package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
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
var State.backtrack: Set<A>? by nullableExtension()
var State.sleep: Set<A>? by nullableExtension()
// GUBED

var Node.backtrack: MutableSet<A>? by nullableExtension()
var Node.sleep: MutableSet<A> by extension()

val Node.explored: Set<A> get() = outEdges.map { it.action }.collect(Collectors.toSet())

/**
 * Dynamic partial order reduction algorithm for state space exploration.
 * @see <a href="https://doi.org/10.1145/3073408">Source Sets: A Foundation for Optimal Dynamic Partial Order Reduction</a>
 */
class XcfaDporLts(private val xcfa: XCFA) : LTS<S, A> {

    private val backTransitions = mutableSetOf<XcfaEdge>()

    init {
        collectBackTransitions()
        System.err.println(xcfa.toDot())
    }

    companion object {
        var random: Random = Random.Default // use Random(seed) with a seed or Random.Default without seed
    }

    private data class StackItem(
        val node: Node,
        val processLastAction: Map<Int, Int> = mutableMapOf(),
        val lastDependents: Map<Int, Map<Int, Int>> = mutableMapOf(),
        val done: MutableSet<A> = mutableSetOf(),
        val mutexLocks: MutableMap<String, Int> = mutableMapOf(),
        private val initialSleep: MutableSet<A> = mutableSetOf()
    ) {
        val action: A get() = node.inEdge.get().action
        val state: S get() = node.state
        var backtrack: MutableSet<A>? by node::backtrack
        var sleep: MutableSet<A> by node::sleep
            private set

        init {
            sleep = initialSleep
        }

        override fun toString() = action.toString()
    }

    private val simpleXcfaLts = getXcfaLts()

    private val stack: Stack<StackItem> = Stack()

    private val last get() = stack.peek()

    private fun getAllEnabledActionsFor(state: S): Set<A> = simpleXcfaLts.getEnabledActionsFor(state)

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
                virtualTraversal(last.node.coveringNode.get(), last.sleep)
            }
            while (stack.isNotEmpty() &&
                (last.node.isSubsumed || last.backtrack?.subtract(last.sleep)?.isEmpty() == true)
            ) {
                if (stack.size >= 2) {
                    val lastButOne = stack[stack.size - 2]
                    if (last.state.isBottom || (last.mutexLocks.containsKey("") &&
                                (last.state.mutexes.keys subtract lastButOne.state.mutexes.keys).contains(""))
                    ) {
                        val disabledDueToLock = getAllEnabledActionsFor(lastButOne.state)
                            .filter {
                                (last.state.isBottom && it != last.node.inEdge.get().action) ||
                                        (it.pid != last.state.mutexes[""] && !lastButOne.sleep.contains(it))
                            }.toSet()
                        val explored = lastButOne.node.outEdges.map { it.action }.collect(Collectors.toSet())
                        if (disabledDueToLock.isNotEmpty() && (explored intersect disabledDueToLock).isEmpty()) {
                            lastButOne.backtrack!!.add(disabledDueToLock.random(random))
                        }
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

        override fun size() = stack.count { it.backtrack == null || it.backtrack!!.isNotEmpty() }

        override fun clear() = stack.clear()

        private fun push(item: Node, virtualLimit: Int) {
            if (!item.inEdge.isPresent) {
                stack.push(StackItem(item))
                return
            }

            val newaction = item.inEdge.get().action
            last.done.add(newaction)
            last.sleep.add(newaction)
            if (backTransitions.contains(newaction.edge)) {
                // TODO replace over-approximation with exact match (covering...)
                last.backtrack = (getAllEnabledActionsFor(last.state) subtract last.done).toMutableSet()
            }

            val process = newaction.pid
            val newProcessLastAction = LinkedHashMap(last.processLastAction).apply { this[process] = stack.size - 1 }
            var newLastDependents: MutableMap<Int, Int> = LinkedHashMap(last.lastDependents[process] ?: mapOf()).apply {
                this[process] = stack.size
            }
            val relevantProcesses = (newProcessLastAction.keys - setOf(process)).toMutableSet()

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

                            val backtrack = stack[index - 1].backtrack!!
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

            // MUTEXES
            val oldMutexes = last.state.mutexes.keys
            val newMutexes = item.state.mutexes.keys
            val lockedMutexes = newMutexes - oldMutexes
            val releasedMutexes = oldMutexes - newMutexes
            releasedMutexes.forEach { m -> last.mutexLocks[m]?.let { stack[it].mutexLocks.remove(m) } }

            val newProcesses = item.state.processes.keys subtract last.state.processes.keys
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
                    initialSleep = last.sleep.filter { !dependent(it, newaction) }.toMutableSet(),
                    mutexLocks = last.mutexLocks.apply {
                        lockedMutexes.forEach { this[it] = stack.size }
                        releasedMutexes.forEach(::remove)
                    }
                )
            )
        }

        private fun virtualTraversal(node: Node, _originalSleep: Set<A>) {
            var originalSleep: Set<A>? = _originalSleep.toSet()
            val originalStackSize = stack.size
            //val originalActions = stack.map { it.action }.toSet() // TODO skip some actions
            val virtualStack = Stack<Node>()
            virtualStack.push(node)
            while (virtualStack.isNotEmpty()) {
                val visiting = virtualStack.pop()
                if (originalSleep != null) { // Reached via a cover edge
                    val sleepDelta = (visiting.sleep subtract originalSleep subtract visiting.explored).toMutableSet()
                    var virtualRoot = visiting
                    while (sleepDelta.isNotEmpty()) {
                        virtualRoot = virtualRoot.parent.get()
                        val intersection = virtualRoot.explored intersect sleepDelta
                        if (intersection.isNotEmpty()) {
                            virtualRoot.outEdges.filter { intersection.contains(it.action) }
                                .forEach { virtualStack.push(it.target) }
                            sleepDelta.removeAll(intersection)
                        }
                    }
                    originalSleep = null
                } else {
                    while (stack.size > originalStackSize && stack.peek().node != visiting.parent.get()) stack.pop()
                    push(visiting, originalStackSize)
                }
                if (visiting.isCovered) {
                    val coveringNode = visiting.coveringNode.get()
                    virtualStack.push(coveringNode)
                    originalSleep = visiting.sleep
                } else {
                    visiting.outEdges.forEach { virtualStack.push(it.target) }
                }
            }
            while (stack.size > originalStackSize) stack.pop()
        }
    }

    override fun getEnabledActionsFor(state: S): Set<A> {
        require(state == last.state)

        val enabledActions = getAllEnabledActionsFor(state) subtract last.sleep
        val enabledProcesses = enabledActions.map { it.pid }.toSet()

        if (last.backtrack == null) {
            if (enabledProcesses.isEmpty()) {
                last.backtrack = mutableSetOf()
                return emptySet()
            }

            last.backtrack = mutableSetOf(enabledActions.random(random))
        }

        val actionToExplore = (last.backtrack!! subtract last.sleep).random() // not empty, see isEmpty
        last.backtrack!!.addAll(enabledActions.filter { it.pid == actionToExplore.pid })
        return setOf(actionToExplore)
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

    private fun collectBackTransitions() {
        // TODO replace with state check in Waitlist::add
        for (procedure in xcfa.procedures) {
            // DFS for every procedure of the XCFA to discover back edges
            val visitedLocations: MutableSet<XcfaLocation> = mutableSetOf()
            val stack = Stack<XcfaLocation>()

            stack.push(procedure.initLoc) // start from the initial location of the procedure
            while (!stack.isEmpty()) {
                val visiting = stack.pop()
                visitedLocations.add(visiting)
                for (outgoingEdge in visiting.outgoingEdges) {
                    val target = outgoingEdge.target
                    if (visitedLocations.contains(target)) { // backward edge
                        backTransitions.add(outgoingEdge)
                    } else {
                        stack.push(target)
                    }
                }
            }
        }
    }
}
