package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.waitlist.Waitlist
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.getGlobalVars
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.*
import java.util.stream.Stream
import kotlin.math.max
import kotlin.random.Random

private typealias S = XcfaState<out ExprState>
private typealias A = XcfaAction

class XcfaDporLts(
    private val xcfa: XCFA
) : LTS<S, A> {

    private val backTransitions = mutableSetOf<XcfaEdge>()

    init {
        collectBackTransitions()
    }

    private val random = Random.Default // or use Random(seed) with a seed

    private data class StackItem(
        val node: ArgNode<out S, A>,
        val processLastAction: Map<Int, Int>,
        val lastDependents: Map<Int, Map<Int, Int>>,
        var backtrack: MutableSet<A>? = null,
        val done: MutableSet<A> = mutableSetOf(),
        var detectedDisabledRaces: Boolean = false,
    ) {
        val action: A get() = node.inEdge.get().action
    }

    private val simpleXcfaLts = getXcfaLts()

    private val stack: Stack<StackItem> = Stack()

    private val last get() = stack.peek()

    private fun getAllEnabledActionsFor(state: S): Set<A> = simpleXcfaLts.getEnabledActionsFor(state)

    val waitlist = object : Waitlist<ArgNode<out S, A>> {

        private fun max(map1: Map<Int, Int>, map2: Map<Int, Int>) =
            (map1.keys union map2.keys).associateWith { key -> max(map1[key] ?: -1, map2[key] ?: -1) }.toMutableMap()

        override fun add(item: ArgNode<out S, A>) {
            if (!item.inEdge.isPresent) {
                stack.push(StackItem(item, LinkedHashMap(), LinkedHashMap()))
                return
            }

            val newaction = item.inEdge.get().action
            val process = newaction.pid
            val newProcessLastAction = LinkedHashMap(last.processLastAction).apply { this[process] = stack.size - 1 }
            var newLastDependents: MutableMap<Int, Int> = LinkedHashMap(last.lastDependents[process] ?: mapOf())
            val relevantProcesses = (newProcessLastAction.keys - setOf(process)).toMutableSet()

            for (index in stack.size - 1 downTo 1) {
                if (relevantProcesses.isEmpty()) break
                val node = stack[index].node
                val action = node.inEdge.get().action
                if (relevantProcesses.contains(action.pid)) {
                    if (index <= (newLastDependents[action.pid] ?: -1)) {
                        // there is an action a' such that  action -> a' -> newaction  (->: happens-before)
                        relevantProcesses.remove(action.pid)
                    } else if (dependent(newaction, action)) {
                        // reversible race
                        val v = notdep(index, newaction)
                        val iv = initials(index, v)
                        val backtrack = stack[index - 1].backtrack!!
                        if ((iv intersect backtrack).isEmpty()) {
                            backtrack.add(iv.random(random))
                        }
                        newLastDependents[action.pid] = index
                        newLastDependents = max(newLastDependents, stack[index].lastDependents[action.pid]!!)
                        relevantProcesses.remove(action.pid)
                    }
                }
            }

            last.done.add(newaction)
            if (backTransitions.contains(newaction.edge)) {
                last.backtrack = (getAllEnabledActionsFor(last.node.state) subtract last.done).toMutableSet()
            }

            stack.push(
                StackItem(
                    node = item,
                    processLastAction = newProcessLastAction,
                    lastDependents = last.lastDependents.toMutableMap().apply { this[process] = newLastDependents },
                )
            )
        }

        override fun addAll(items: Collection<ArgNode<out S, A>>) {
            assert(items.size == 1) // TODO <=
            add(items.first())
        }

        override fun addAll(items: Stream<out ArgNode<out S, A>>) {
            val iterator = items.iterator()
            add(iterator.next()) // TODO if (iterator.hasNext())
            assert(!iterator.hasNext())
        }

        override fun isEmpty() = stack.isEmpty()

        override fun remove(): ArgNode<out S, A> {
            if (isEmpty) throw NoSuchElementException("The search stack is empty.")
            return stack.peek().node
        }

        override fun size() = stack.count { it.backtrack == null || it.backtrack!!.isNotEmpty() }

        override fun clear() = stack.clear()
    }

    override fun getEnabledActionsFor(state: S): Set<A> {
        assert(state == last.node.state)

        val enabledActions = getAllEnabledActionsFor(state)
        val enabledProcesses = enabledActions.map { it.pid }.toSet()

        if (!last.detectedDisabledRaces && state.processes.size != enabledProcesses.size && state.mutexes.containsKey("")) {
            // TODO check enabled transition instead of enabled processes (this way, it may not work with LBE)
            // TODO proper disabled race detection
            last.backtrack = enabledActions.toMutableSet()
            last.detectedDisabledRaces = true
        }

        if (enabledProcesses.isEmpty()) {
            do stack.pop() while (stack.isNotEmpty() && last.backtrack!!.isEmpty())
            return emptySet()
        }

        if (last.backtrack == null) {
            val randomProcess = enabledProcesses.random(random)
            last.backtrack = enabledActions.filter { it.pid == randomProcess }.toMutableSet()
        }

        val actionToExplore = last.backtrack!!.random()
        last.backtrack!!.remove(actionToExplore)

        return setOf(actionToExplore)
    }

    private fun dependent(a: A, b: A): Boolean {
        if (a.pid == b.pid) return true

        // TODO caching...
        val aGlobalVars = a.edge.getGlobalVars(xcfa)
        val bGlobalVars = b.edge.getGlobalVars(xcfa)
        if ((aGlobalVars.keys intersect bGlobalVars.keys).any { aGlobalVars[it] == true || bGlobalVars[it] == true }) {
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
