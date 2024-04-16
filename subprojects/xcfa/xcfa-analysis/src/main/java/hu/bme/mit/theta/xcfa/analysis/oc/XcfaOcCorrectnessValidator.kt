package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import java.io.File
import kotlin.time.ExperimentalTime
import kotlin.time.measureTime

@OptIn(ExperimentalTime::class)
internal class XcfaOcCorrectnessValidator(
    decisionProcedure: OcDecisionProcedureType,
    private val inputConflictClauseFile: String,
    private val threads: Set<Thread>,
    private val ocChecker: OcChecker<E> = decisionProcedure.checker(),
) : OcChecker<E> by ocChecker {

    private var clauseValidationTime = 0L
    private lateinit var reachableEdges: Map<Int, ReachableEdges>

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>, pos: List<Relation<E>>, rfs: Map<VarDecl<*>, List<Relation<E>>>
    ): SolverStatus? {
        val flatRfs = rfs.values.flatten()
        val flatEvents = events.values.flatMap { it.values.flatten() }
        val parser = XcfaOcReasonParser(flatRfs.toSet(), flatEvents.toSet())
        var parseFailure = 0
        val propagatedClauses = File(inputConflictClauseFile).readLines().mapNotNull { line ->
            try {
                parser.parse(line)
            } catch (_: Exception) {
                parseFailure++
                null
            }
        }

        clauseValidationTime += measureTime {
            reachableEdges = threads.associate { it.pid to ReachableEdges(it.procedure) }
        }.inWholeMilliseconds

        val validConflicts: List<Reason>
        clauseValidationTime += measureTime {
            validConflicts = propagatedClauses.filter { clause -> checkPath(clause) }
        }.inWholeMilliseconds
        System.err.println("Conflict clause parse failures: $parseFailure")
        System.err.println("Parsed conflict clauses: ${propagatedClauses.size}")
        System.err.println("Validated conflict clauses: ${validConflicts.size}")
        System.err.println("Clause validation time (ms): $clauseValidationTime")

        ocChecker.solver.add(validConflicts.map { Not(it.expr) })
        val result: SolverStatus?
        System.err.println("Solver time (ms): " + measureTime {
            result = ocChecker.check(events, pos, rfs)
        }.inWholeMilliseconds)
        return result
    }

    private fun checkPath(combinedReason: Reason, from: E? = null, to: E? = null): Boolean {
        val reasons = combinedReason.reasons.filter { r ->
            when (r) {
                is RelationReason<*>, is WriteSerializationReason<*>, is FromReadReason<*> ->
                    if (r.derivable()) true else return false

                is PoReason -> false
                else -> return false
            }
        }
        if (reasons.isEmpty()) return if (from != null) isPo(from, to!!) else false

        var possibleOrders = if (from == null) {
            listOf(listOf(reasons.first()) to reasons.slice(1 until reasons.size))
        } else {
            reasons.filter { isPo(from, it.from) }.map { listOf(it) to reasons - it }
        }

        for (i in 1 until reasons.size) {
            val newPossibleOrders = mutableListOf<Pair<List<Reason>, List<Reason>>>()
            possibleOrders.forEach { po ->
                val previous = po.first.last()
                po.second.filter { isPo(previous.to, it.from) }.forEach { next ->
                    newPossibleOrders.add(po.first + next to po.second - next)
                }
            }
            possibleOrders = newPossibleOrders
        }

        if (from != null) return possibleOrders.any { isPo(it.first.last().to, to!!) }
        return possibleOrders.any { isPo(it.first.last().to, it.first.first().from) } // check cylce
    }

    private fun isRf(rf: Relation<*>): Boolean =
        rf.from.const.varDecl == rf.to.const.varDecl && rf.from.type == EventType.WRITE && rf.to.type == EventType.READ

    private fun derivable(rf: Relation<*>, w: Event): Boolean =
        isRf(rf) && rf.from.const.varDecl == w.const.varDecl && w.type == EventType.WRITE

    private fun Reason.derivable(): Boolean = when (this) {
        is PoReason -> false
        is CombinedReason -> reasons.all { it.derivable() }
        is RelationReason<*> -> isRf(this.relation)
        is WriteSerializationReason<*> -> {
            this as WriteSerializationReason<E>
            if (!derivable(rf, w)) false
            else checkPath(wBeforeRf, w, rf.to)
        }

        is FromReadReason<*> -> {
            this as FromReadReason<E>
            if (!derivable(rf, w)) false
            else checkPath(wAfterRf, rf.from, w)
        }
    }

    private val Reason.from: E
        get() = when (this) {
            is RelationReason<*> -> (this as RelationReason<E>).relation.from
            is WriteSerializationReason<*> -> (this as WriteSerializationReason<E>).w
            is FromReadReason<*> -> (this as FromReadReason<E>).rf.to
            else -> error("Unsupported reason type.")
        }

    private val Reason.to: E
        get() = when (this) {
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