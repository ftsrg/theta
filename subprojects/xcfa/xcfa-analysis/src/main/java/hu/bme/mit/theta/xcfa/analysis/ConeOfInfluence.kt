package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import kotlin.math.max
import kotlin.math.min

lateinit var COI: ConeOfInfluence

private typealias S = XcfaState<out ExprState>
private typealias A = XcfaAction

class ConeOfInfluence(
    private val xcfa: XCFA,
    var coreLts: LTS<S, A> = getXcfaLts()
) {

    private var lastPrec: Prec? = null

    private val edgeToProcedure: MutableMap<XcfaEdge, XcfaProcedure> = mutableMapOf()
    private val locToScc: MutableMap<XcfaLocation, Int> = mutableMapOf()

    private val directObservers: MutableMap<XcfaEdge, MutableSet<XcfaEdge>> = mutableMapOf()
    private val interProcessObservers: MutableMap<XcfaEdge, MutableSet<XcfaEdge>> = mutableMapOf()

    val lts = object : LTS<S, A> {
        override fun getEnabledActionsFor(state: S): Collection<A> {
            val enabled = coreLts.getEnabledActionsFor(state)
            return replaceIrrelevantActions(state, enabled)
        }

        override fun <P : Prec> getEnabledActionsFor(state: S, explored: Collection<A>, prec: P): Collection<A> {
            if (lastPrec != prec) reinitialize(prec)
            val enabled = coreLts.getEnabledActionsFor(state, explored, prec)
            return replaceIrrelevantActions(state, enabled)
        }

        private fun replaceIrrelevantActions(state: S, enabled: Collection<A>): Collection<A> {
            if (lastPrec == null) return enabled

            val procedures = state.processes.map { (p, pState) ->
                val loc = pState.locs.peek()
                val procedure = edgeToProcedure[loc.incomingEdges.ifEmpty(loc::outgoingEdges).first()]!!
                p to Pair(procedure, locToScc[loc]!!)
            }.toMap()
            return enabled.map { action ->
                val otherProcedures = procedures.filter { it.key != action.pid }.values.fold(
                    mutableMapOf<XcfaProcedure, Int>()) { acc, next ->
                    acc[next.first] = max(next.second, acc[next.first] ?: 0)
                    acc
                }
                if (!isObserved(action, otherProcedures)) {
                    replace(action)
                } else {
                    action
                }
            }
        }

        private fun isObserved(action: A, otherProcedures: Map<XcfaProcedure, Int>): Boolean {
            val toVisit = edgeToProcedure.keys.filter {
                it.source == action.edge.source && it.target == action.edge.target
            }.toMutableList()
            while (toVisit.isNotEmpty()) {
                val visiting = toVisit.removeFirst()
                if (isRealObserver(visiting)) return true

                toVisit.addAll(directObservers[visiting] ?: emptySet())
                toVisit.addAll(interProcessObservers[visiting]?.filter { edge ->
                    otherProcedures.containsKey(edgeToProcedure[edge]) &&
                        otherProcedures[edgeToProcedure[edge]]!! > locToScc[edge.source]!! // the edge is still reachable
                } ?: emptySet())
            }
            return false
        }

        private fun replace(action: A) = action.withLabel(action.label.replace().run {
            if (this !is SequenceLabel) SequenceLabel(listOf(this)) else this
        })

        private fun XcfaLabel.replace(): XcfaLabel = when {
            this is SequenceLabel -> SequenceLabel(labels.map { it.replace() }, metadata)
            this is NondetLabel -> NondetLabel(labels.map { it.replace() }.toSet(), metadata)
            this is StmtLabel && (this.stmt is AssignStmt<*> || this.stmt is HavocStmt<*>) -> NopLabel
            else -> this
        }
    }

    init {
        xcfa.procedures.forEach { tarjan(it.initLoc) }
    }

    fun reinitialize(prec: Prec) {
        directObservers.clear()
        interProcessObservers.clear()
        xcfa.procedures.forEach { procedure ->
            procedure.edges.forEach {
                edgeToProcedure[it] = procedure
                findDirectObservers(it, prec)
                findInterProcessObservers(it, prec)
            }
        }
        lastPrec = prec

        System.err.println("Direct:")
        directObservers.forEach { (k, v) -> System.err.println("${k.label} -> ${v.map { it.label }}") }
        System.err.println("Indirect:")
        interProcessObservers.forEach { (k, v) -> System.err.println("${k.label} -> ${v.map { it.label }}") }
    }


    private fun tarjan(initLoc: XcfaLocation) {
        var sccCnt = 0
        var discCnt = 0
        val disc = mutableMapOf<XcfaLocation, Int>()
        val lowest = mutableMapOf<XcfaLocation, Int>()
        val visited = mutableSetOf<XcfaLocation>()
        val stack = Stack<XcfaLocation>()
        val toVisit = Stack<XcfaLocation>()
        toVisit.push(initLoc)

        while (toVisit.isNotEmpty()) {
            val visiting = toVisit.peek()
            if (visiting !in visited) {
                disc[visiting] = discCnt++
                lowest[visiting] = disc[visiting]!!
                stack.push(visiting)
                visited.add(visiting)
            }

            for (edge in visiting.outgoingEdges) {
                if (edge.target in stack) {
                    lowest[visiting] = min(lowest[visiting]!!, lowest[edge.target]!!)
                } else if (edge.target !in visited) {
                    toVisit.push(edge.target)
                    break
                }
            }

            if (toVisit.peek() != visiting) continue

            if (lowest[visiting] == disc[visiting]) {
                val scc = sccCnt++
                while (stack.peek() != visiting) {
                    locToScc[stack.pop()] = scc
                }
                locToScc[stack.pop()] = scc // visiting
            }

            toVisit.pop()
        }
    }


    private fun isRealObserver(edge: XcfaEdge) = edge.label.collectAssumesVars().isNotEmpty()

    private fun findDirectObservers(edge: XcfaEdge, prec: Prec) {
        val precVars = prec.usedVars
        val writtenVars = edge.getVars().filter { it.value.isWritten && it.key in precVars }
        if (writtenVars.isEmpty()) return

        val toVisit = mutableListOf(edge)
        val visited = mutableSetOf<XcfaEdge>()
        while (toVisit.isNotEmpty()) {
            val visiting = toVisit.removeFirst()
            visited.add(visiting)
            addEdgeIfObserved(edge, visiting, writtenVars, precVars, directObservers)
            toVisit.addAll(visiting.target.outgoingEdges.filter { it !in visited })
        }
    }

    private fun findInterProcessObservers(edge: XcfaEdge, prec: Prec) {
        val precVars = prec.usedVars
        val writtenVars = edge.getVars().filter { it.value.isWritten && it.key in precVars }
        if (writtenVars.isEmpty()) return

        xcfa.procedures.forEach { procedure ->
            procedure.edges.forEach {
                addEdgeIfObserved(edge, it, writtenVars, precVars, interProcessObservers)
            }
        }
    }

    private fun addEdgeIfObserved(
        source: XcfaEdge, target: XcfaEdge, observableVars: Map<VarDecl<*>, AccessType>,
        precVars: Collection<VarDecl<*>>, relation: MutableMap<XcfaEdge, MutableSet<XcfaEdge>>
    ) {
        val vars = target.getVars()
        var relevantAction = vars.any { it.value.isWritten && it.key in precVars }
        if (!relevantAction) {
            val assumeVars = target.label.collectAssumesVars()
            relevantAction = assumeVars.any { it in precVars }
        }

        if (relevantAction && vars.any { it.key in observableVars && it.value.isRead }) {
            relation[source] = relation[source] ?: mutableSetOf()
            relation[source]!!.add(target)
        }
    }

}