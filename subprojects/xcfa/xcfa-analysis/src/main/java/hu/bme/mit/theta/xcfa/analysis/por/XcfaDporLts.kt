package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.isRead
import hu.bme.mit.theta.xcfa.isWritten
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
    private val map = IdentityHashMap<R, T>()
    override fun getValue(thisRef: R, property: KProperty<*>) = map[thisRef]!!
    override fun setValue(thisRef: R, property: KProperty<*>, value: T) {
        map[thisRef] = value
    }
}

private open class NullableExtensionProperty<R, T> : ReadWriteProperty<R, T?> {
    protected val map = IdentityHashMap<R, T?>()
    override fun getValue(thisRef: R, property: KProperty<*>) = map[thisRef]
    override fun setValue(thisRef: R, property: KProperty<*>, value: T?) {
        map[thisRef] = value
    }

    fun clear() = map.clear()
}

private fun <R, T> extension() = ExtensionProperty<R, T>()
private fun <R, T> nullableExtension() = NullableExtensionProperty<R, T?>()

// DEBUG
var State.reachedNumber: Int? by nullableExtension()
var _xcfa: XCFA? = null
fun Set<A>.toStr() = "${
    map {
        val vars = it.edge.getGlobalVars(_xcfa!!)
        "${it.pid}: ${it.source} -> ${it.target} W${vars.filter { e -> e.value.isWritten }.keys.map { v -> v.name }} R${vars.filter { e -> e.value.isRead }.keys.map { v -> v.name }}"
    }
}"
// GUBED

var State.backtrack: MutableSet<A> by extension() // TODO private
var State.sleep: MutableSet<A> by extension() // TODO private
var State.explored: MutableSet<A> by extension() // TODO private

private val reExploredDelegate = nullableExtension<State, Boolean?>()
private var State.reExplored: Boolean? by reExploredDelegate
private var A.varLookUp: Map<VarDecl<*>, VarDecl<*>> by extension()

private val Node.explored: Set<A> get() = outEdges.map { it.action }.collect(Collectors.toSet())

/**
 * Dynamic partial order reduction (DPOR) algorithm for state space exploration.
 * @see <a href="https://doi.org/10.1145/3073408">Source Sets: A Foundation for Optimal Dynamic Partial Order Reduction</a>
 */
open class XcfaDporLts(private val xcfa: XCFA) : LTS<S, A> {

    init {
        _xcfa = xcfa
        //System.err.println(xcfa.toDot())
    }

    companion object {
        var random: Random = Random.Default // use Random(seed) with a seed or Random.Default without seed

        private val simpleXcfaLts = getXcfaLts()

        private val State.enabled: Set<A>
            get() {
                val enabledActions = simpleXcfaLts.getEnabledActionsFor(this as S)
                enabledActions.forEach { it.varLookUp = this.processes[it.pid]!!.varLookup.peek() }
                return enabledActions
            }

        fun <E : ExprState> getPartialOrder(partialOrd: PartialOrd<E>) =
            PartialOrd<E> { s1, s2 ->
                partialOrd.isLeq(s1, s2) && s2.reExplored == true && s1.sleep.containsAll(s2.sleep - s2.explored)
            }
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

        var explored: MutableSet<A> by node.state::explored
            private set

        init {
            backtrack = _backtrack
            sleep = _sleep
            explored = mutableSetOf()
        }

        override fun toString() = action.toString()
    }

    private val stack: Stack<StackItem> = Stack()

    private val last get() = stack.peek()

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

    val waitlist = object : Waitlist<Node> {

        var counter = 0

        override fun add(item: Node) {
            var node = item
            while (stack.isEmpty() && node.parent.isPresent) node = node.parent.get()

            node.state.reachedNumber = counter++
            node.state.reExplored = true
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

        override fun isEmpty(): Boolean {
            if (last.node.isCovered && last.node.isFeasible) {
                virtualExploration(last.node.coveringNode.get(), stack.size)
            } else {
                exploreLazily()
            }
            while (stack.isNotEmpty() &&
                (last.node.isSubsumed || (last.node.isExpanded && last.backtrack.subtract(last.sleep).isEmpty()))
            ) {
                if (stack.size >= 2) {
                    val lastButOne = stack[stack.size - 2]
                    val mutexNeverReleased = last.mutexLocks.containsKey("") &&
                            (last.state.mutexes.keys subtract lastButOne.state.mutexes.keys).contains("")
                    if (last.node.explored.isEmpty() || mutexNeverReleased) {
                        lastButOne.backtrack = lastButOne.state.enabled.toMutableSet()
                    }
                }
                stack.pop()
                exploreLazily()
            }
            return stack.isEmpty()
        }

        override fun remove(): Node {
            if (isEmpty) throw NoSuchElementException("The search stack is empty.")
            return last.node
        }

        override fun size() = stack.size

        override fun clear() {
            stack.clear()
            reExploredDelegate.clear()
        }

        private fun push(item: Node, virtualLimit: Int): Boolean {
            if (!item.inEdge.isPresent) {
                stack.push(StackItem(item, _backtrack = item.state.enabled.toMutableSet()))
                return true
            }

            val newaction = item.inEdge.get().action
            val process = newaction.pid
            newaction.varLookUp = item.parent.get().state.processes[process]!!.varLookup.peek()

            val newProcessLastAction = LinkedHashMap(last.processLastAction).apply { this[process] = stack.size }
            var newLastDependents: MutableMap<Int, Int> = LinkedHashMap(last.lastDependents[process] ?: mapOf()).apply {
                this[process] = stack.size
            }
            val relevantProcesses = (newProcessLastAction.keys - setOf(process)).toMutableSet()

            // Race detection
            for (index in stack.size - 1 downTo 1) {
                if (relevantProcesses.isEmpty()) break
                val node = stack[index].node
                if (node.parent.get() != stack[index - 1].node) continue // skip covering node

                val action = node.inEdge.get().action
                if (relevantProcesses.contains(action.pid)) {
                    if (newLastDependents.containsKey(action.pid) && index <= newLastDependents[action.pid]!!) {
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

            val isCoveringNode = item.parent.get() != last.node
            val isVirtualExploration = virtualLimit < stack.size || isCoveringNode
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

            stack.push(
                StackItem(
                    node = item,
                    processLastAction = if (!isCoveringNode) newProcessLastAction else last.processLastAction.toMutableMap(),
                    lastDependents = last.lastDependents.toMutableMap().apply {
                        if (!isCoveringNode) {
                            this[process] = newLastDependents
                            newProcesses.forEach {
                                this[it] = max(this[it] ?: mutableMapOf(), newLastDependents)
                            }
                        }
                    },
                    mutexLocks = last.mutexLocks.apply {
                        lockedMutexes.forEach { this[it] = stack.size }
                        releasedMutexes.forEach(::remove)
                    },
                    _backtrack = newBacktrack,
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

                if (!push(visiting, startStackSize) || noInfluenceOnRealExploration(realStackSize)) continue

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

        private fun exploreLazily() {
            while (stack.isNotEmpty()) {
                val lazilyExplorable = last.node.outEdges
                    .filter { it.target.state.reExplored != true && it.action !in last.sleep }
                    .collect(Collectors.toSet())
                if (lazilyExplorable.isEmpty()) return

                val edgeToExplore = lazilyExplorable.random(random)
                val actionToExplore = edgeToExplore.action
                last.backtrack.addAll(last.state.enabled.filter { it.pid == actionToExplore.pid })
                last.sleep.add(actionToExplore)
                last.explored.add(actionToExplore)
                add(edgeToExplore.target)
            }
        }

        private fun max(map1: Map<Int, Int>, map2: Map<Int, Int>) =
            (map1.keys union map2.keys).associateWith { key -> max(map1[key] ?: -1, map2[key] ?: -1) }.toMutableMap()

        private fun notdep(start: Int, action: A): List<A> {
            val e = stack[start].action
            return stack.slice(start + 1 until stack.size)
                .filterIndexed { index, item ->
                    item.node.parent.get() == stack[start + 1 + index - 1].node && !dependent(e, item.action)
                }
                .map { it.action }
                .toMutableList().apply { add(action) }
        }

        private fun initials(start: Int, sequence: List<A>): Set<A> {
            val state = stack[start].node.state
            return (state.enabled subtract state.sleep).filter { enabledAction ->
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

    protected open fun dependent(a: A, b: A): Boolean {
        if (a.pid == b.pid) return true

        val aGlobalVars = a.edge.getGlobalVars(xcfa)
        val bGlobalVars = b.edge.getGlobalVars(xcfa)
        // dependent if they access the same variable (at least one write)
        return (aGlobalVars.keys intersect bGlobalVars.keys)
            .any { aGlobalVars[it].isWritten || bGlobalVars[it].isWritten }
    }
}

/**
 * Abstraction-aware dynamic partial order reduction (AADPOR) algorithm for state space exploration.
 */
class XcfaAadporLts(private val xcfa: XCFA) : XcfaDporLts(xcfa) {

    private lateinit var prec: Prec

    override fun <P : Prec> getEnabledActionsFor(state: S, exploredActions: Collection<A>, prec: P): Set<A> {
        this.prec = prec
        return getEnabledActionsFor(state)
    }

    override fun dependent(a: A, b: A): Boolean {
        if (a.pid == b.pid) return true

        val precVars = prec.usedVars.flatMap { precVar ->
            buildList<VarDecl<*>> {
                add(precVar)
                a.varLookUp[precVar]?.let { add(it) }
                b.varLookUp[precVar]?.let { add(it) }
            }
        }.toSet()
        val aGlobalVars = a.edge.getGlobalVars(xcfa, precVars)
        val bGlobalVars = b.edge.getGlobalVars(xcfa, precVars)
        // dependent if they access the same variable in the precision (at least one write)
        return (aGlobalVars.keys intersect bGlobalVars.keys intersect precVars)
            .any { aGlobalVars[it].isWritten || bGlobalVars[it].isWritten }
    }
}
