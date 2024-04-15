package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.*
import kotlin.math.min
import kotlin.time.ExperimentalTime
import kotlin.time.measureTime

@OptIn(ExperimentalTime::class)
internal class XcfaOcCorrectnessValidator(
    decisionProcedure: OcDecisionProcedureType,
    private val ocChecker: OcChecker<E>,
    threads: Set<Thread>,
    private val events: Map<VarDecl<*>, Map<Int, List<E>>>,
    private val pos: List<R>,
    private val rfs: Map<VarDecl<*>, List<R>>
) {

    private var clauseValidationTime = 0L
    internal val ocCorrectnessValidator: OcChecker<E> = decisionProcedure.checker()
    private val reachableEdges: Map<Int, ReachableEdges>

    init {
        clauseValidationTime += measureTime {
            reachableEdges = threads.associate { it.pid to ReachableEdges(it.procedure.initLoc) }
        }.inWholeMilliseconds
    }

    fun validate(): Boolean {
        check(ocChecker.solver.status.isUnsat)
        val propagated = ocChecker.getPropagatedClauses()
        val validConflicts: List<Reason>
        clauseValidationTime += measureTime {
            validConflicts = propagated.filter { clause -> checkCycle(clause) }
        }.inWholeMilliseconds
        System.err.println("All conflict clauses: ${propagated.size}")
        System.err.println("Validated conflict clauses: ${validConflicts.size}")
        System.err.println("Clause validation time (ms): $clauseValidationTime")

        events.values.flatMap { it.values.flatten() }.forEach { it.enabled = null }
        rfs.values.flatten().forEach { it.enabled = null }
        //ocCorrectnessValidator.solver.add(validConflicts.map { Not(it.expr) })

        val result = ocCorrectnessValidator.check(events, pos, rfs)?.isUnsat == true
        return result
    }

    private fun checkCycle(combinedReason: Reason): Boolean {
        if (combinedReason.reasons.isEmpty()) return false
        var firstEvent: E? = null
        var previousEvent: E? = null
        combinedReason.reasons.forEach { r ->
            when (r) {
                is RelationReason<*> -> {
                    if (!isRf(r.relation)) return false
                    r as RelationReason<E>
                    r.relation.from to r.relation.to
                }

                is WriteSerializationReason<*> -> {
                    if (!derivable(r.rf, r.w)) return false
                    r as WriteSerializationReason<E>
                    r.w to r.rf.from
                }

                is FromReadReason<*> -> {
                    if (!derivable(r.rf, r.w)) return false
                    r as FromReadReason<E>
                    r.rf.to to r.w
                }

                is PoReason -> null
                else -> error("Nested combined reasons or other unknown reasons not supported.")
            }?.let { order ->
                if (!isPo(previousEvent, order.first)) return false
                if (firstEvent == null) firstEvent = order.first
                previousEvent = order.second
            }
        }
        return isPo(previousEvent, firstEvent!!)
    }

    private fun isPo(from: E?, to: E): Boolean {
        from ?: return true
        if (from.pid != to.pid) return false
        return reachableEdges[from.pid]!!.reachable(from.edge, to.edge)
    }

    private fun isRf(rf: Relation<*>): Boolean =
        rf.from.const.varDecl == rf.to.const.varDecl && rf.from.type == EventType.WRITE && rf.to.type == EventType.READ

    private fun derivable(rf: Relation<*>, w: Event): Boolean {
        return isRf(rf) && rf.from.const.varDecl == w.const.varDecl && w.type == EventType.WRITE
    }

    private class ReachableEdges(initLoc: XcfaLocation) {

        private data class Edge(val source: XcfaLocation?, val target: XcfaLocation) {
            constructor(edge: XcfaEdge) : this(edge.source, edge.target)
        }

        private infix fun XcfaLocation?.to(other: XcfaLocation) = Edge(this, other)

        private val heads: MutableList<Edge> = mutableListOf()
        private var sccCnt = 0
        private val sccs = mutableMapOf<Edge, Int>()
        private var reachable: Array<Array<Boolean>>

        init {
            tarjan(initLoc)
            reachable = Array(sccCnt) { Array(sccCnt) { false } }
            val initials = mutableListOf<Pair<Int, Int>>()
            heads.forEach { head ->
                head.source?.incomingEdges?.forEach {
                    val incoming = Edge(it)
                    initials.add(sccs[incoming]!! to sccs[head]!!)
                    reachable[sccs[incoming]!!][sccs[head]!!] = true
                }
            }
            close(initials) // close reachable transitively
        }

        fun reachable(from: XcfaEdge, to: XcfaEdge): Boolean = reachable[sccs[Edge(from)]!!][sccs[Edge(to)]!!]

        private fun tarjan(initLoc: XcfaLocation) {
            var discCnt = 0
            val disc = mutableMapOf<Edge, Int>()
            val lowest = mutableMapOf<Edge, Int>()
            val visited = mutableSetOf<Edge>()
            val stack = Stack<Edge>()
            val toVisit = Stack<Edge>()
            toVisit.push(null to initLoc)

            while (toVisit.isNotEmpty()) {
                val visiting = toVisit.peek()
                if (visiting !in visited) {
                    disc[visiting] = discCnt++
                    lowest[visiting] = disc[visiting]!!
                    stack.push(visiting)
                    visited.add(visiting)
                }

                for (e in visiting.target.outgoingEdges) {
                    val edge = Edge(e)
                    if (edge in stack) {
                        lowest[visiting] = min(lowest[visiting]!!, lowest[edge]!!)
                    } else if (edge !in visited) {
                        toVisit.push(edge)
                        break
                    }
                }

                if (toVisit.peek() != visiting) continue

                if (lowest[visiting] == disc[visiting]) { // new head found
                    val scc = sccCnt++
                    while (stack.peek() != visiting) {
                        sccs[stack.pop()] = scc
                    }
                    sccs[stack.pop()] = scc // visiting
                    heads.add(visiting)
                }

                toVisit.pop()
            }
        }

        private fun close(initials: List<Pair<Int, Int>>) {
            val toClose = initials.toMutableList()
            while (toClose.isNotEmpty()) {
                val (from, to) = toClose.removeFirst()
                if (reachable[from][to]) continue

                reachable[from][to] = true
                reachable[to].forEachIndexed { i, b ->
                    if (b && !reachable[from][i]) toClose.add(from to i)
                }
                reachable.forEachIndexed { i, b ->
                    if (b[from] && !reachable[i][to]) toClose.add(i to to)
                }
            }
        }
    }
}