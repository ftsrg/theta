package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

internal class XcfaExactPo(private val threads: Set<Thread>) {

    private val reachableEdges = threads.associate { it.pid to ReachableEdges(it.procedure) }

    private data class Edge(val source: XcfaLocation?, val target: XcfaLocation, val pid: Int) {

        val edge: Pair<XcfaLocation?, XcfaLocation> get() = source to target

        constructor(event: E) : this(event.edge.source, event.edge.target, event.pid)
    }

    fun isPo(from: E?, to: E): Boolean {
        from ?: return true
        if (Edge(from) == Edge(to)) return from.id < to.id
        val possiblePathPoints = mutableListOf(Edge(from))
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
                source?.incomingEdges?.filter { Edge(it) in ids }?.forEach { initials.add(ids[Edge(it)]!! to id) }
            }
            target.outgoingEdges.filter { Edge(it) in ids }.forEach { initials.add(id to ids[Edge(it)]!!) }

            val toAdd = target.outgoingEdges.map { it.source to it.target }.filter { it !in ids && it !in toVisit }
            toVisit.addAll(toAdd)
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