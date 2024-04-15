package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import kotlin.time.ExperimentalTime
import kotlin.time.measureTime

@OptIn(ExperimentalTime::class)
internal class XcfaOcCorrectnessValidator(
    decisionProcedure: OcDecisionProcedureType,
    private val ocChecker: OcChecker<E>,
    private val threads: Set<Thread>,
    private val events: Map<VarDecl<*>, Map<Int, List<E>>>,
    private val pos: List<R>,
    private val rfs: Map<VarDecl<*>, List<R>>
) {

    private var clauseValidationTime = 0L
    internal val ocCorrectnessValidator: OcChecker<E> = decisionProcedure.checker()
    private val reachableEdges: Map<Int, ReachableEdges>

    init {
        clauseValidationTime += measureTime {
            reachableEdges = threads.associate { it.pid to ReachableEdges(it.procedure) }
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
        ocCorrectnessValidator.solver.add(validConflicts.map { Not(it.expr) })

        val result = ocCorrectnessValidator.check(events, pos, rfs)?.isUnsat == true
        return result
    }

    private fun checkCycle(combinedReason: Reason): Boolean {
        val reasons = combinedReason.reasons.filter { r ->
            when (r) {
                is RelationReason<*> -> if (isRf(r.relation)) true else return false
                is WriteSerializationReason<*> -> if (derivable(r.rf, r.w)) true else return false
                is FromReadReason<*> -> if (derivable(r.rf, r.w)) true else return false
                is PoReason -> false
                else -> return false
            }
        }
        if (reasons.isEmpty()) return false

        var possibleOrders = listOf(listOf(reasons.first()) to reasons.slice(1 until reasons.size))
        for (i in 1 until reasons.size) {
            val newPossibleOrders = mutableListOf<Pair<List<Reason>, List<Reason>>>()
            possibleOrders.forEach { po ->
                val previous = po.first.last()
                po.second.filter { isPo(previous.to, it.from) }.forEach{ next ->
                    newPossibleOrders.add(po.first + next to po.second - next)
                }
            }
            possibleOrders = newPossibleOrders
        }
        return possibleOrders.any { isPo(it.first.last().to, it.first.first().from) }
    }

    private fun isRf(rf: Relation<*>): Boolean =
        rf.from.const.varDecl == rf.to.const.varDecl && rf.from.type == EventType.WRITE && rf.to.type == EventType.READ

    private fun derivable(rf: Relation<*>, w: Event): Boolean {
        return isRf(rf) && rf.from.const.varDecl == w.const.varDecl && w.type == EventType.WRITE
    }

    private val Reason.from: E get() = when (this) {
        is RelationReason<*> -> (this as RelationReason<E>).relation.from
        is WriteSerializationReason<*> -> (this as WriteSerializationReason<E>).w
        is FromReadReason<*> -> (this as FromReadReason<E>).rf.to
        else -> error("Unsupported reason type.")
    }

    private val Reason.to: E get() = when (this) {
        is RelationReason<*> -> (this as RelationReason<E>).relation.to
        is WriteSerializationReason<*> -> (this as WriteSerializationReason<E>).rf.from
        is FromReadReason<*> -> (this as FromReadReason<E>).w
        else -> error("Unsupported reason type.")
    }

    private fun isPo(from: E?, to: E): Boolean {
        data class Edge(val source: XcfaLocation?, val target: XcfaLocation, val pid: Int) {

            val edge: Pair<XcfaLocation?, XcfaLocation> get() = source to target

            constructor(event: E) : this(event.edge.source, event.edge.target, event.pid)
        }

        val possiblePathPoints = mutableListOf(Edge(from ?: return true))
        val visited = mutableSetOf<Edge>()
        while (possiblePathPoints.isNotEmpty()) {
            val current = possiblePathPoints.removeFirst()
            if (!visited.add(current)) continue
            if (current.pid == to.pid && reachableEdges[current.pid]!!.reachable(current.edge, to.edge)) return true

            threads.filter {
                it.startEvent?.pid == current.pid &&
                    reachableEdges[current.pid]!!.reachable(current.edge, it.startEvent.edge)
            }.forEach { thread ->
                possiblePathPoints.add(Edge(null, thread.procedure.initLoc, thread.pid))
            }

            threads.find { it.pid == current.pid }?.let { thread ->
                thread.joinEvents.forEach { possiblePathPoints.add(Edge(it.edge.source, it.edge.target, it.pid)) }
            }
        }

        return false
    }

    private class ReachableEdges(procedure: XcfaProcedure) {

        private data class Edge(val source: XcfaLocation?, val target: XcfaLocation) {
            constructor(edge: XcfaEdge) : this(edge.source, edge.target)
        }

        private infix fun XcfaLocation?.to(other: XcfaLocation) = Edge(this, other)

        private val ids = mutableMapOf<Edge, Int>()
        private var reachable: Array<Array<Boolean>>

        init {
            val toVisit = mutableListOf(null to procedure.initLoc)
            val initials = mutableListOf<Pair<Int, Int>>()
            while (toVisit.isNotEmpty()) { // assumes xcfa contains no cycles (an OC checker requirement)
                val (source, target) = toVisit.removeFirst()
                val id = ids.size
                ids[source to target] = id
                if (source == procedure.initLoc) {
                    initials.add(ids[null to procedure.initLoc]!! to id)
                } else {
                    source?.incomingEdges?.forEach { initials.add(ids[it.source to it.target]!! to id) }
                }
                toVisit.addAll(target.outgoingEdges.map { it.source to it.target })
            }
            reachable = Array(ids.size) { Array(ids.size) { false } }
            close(initials) // close reachable transitively
        }

        fun reachable(from: Pair<XcfaLocation?, XcfaLocation>, to: XcfaEdge): Boolean =
            reachable[ids[from.first to from.second]!!][ids[Edge(to)]!!]

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
            for (i in reachable.indices) reachable[i][i] = true
        }
    }
}