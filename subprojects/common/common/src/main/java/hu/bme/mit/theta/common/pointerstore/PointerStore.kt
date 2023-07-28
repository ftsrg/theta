package hu.bme.mit.theta.common.pointerstore

import hu.bme.mit.theta.common.visualization.*
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import java.awt.Color
import java.util.UUID

class PointerStore<T> {
    private val pointerStoreMembers: MutableSet<T> = mutableSetOf()
    private val pointsTo: MutableSet<Pair<T, T>> = mutableSetOf()

    fun addPointer(pointerStoreMember: T) {
        pointerStoreMembers.add(pointerStoreMember)
    }

    fun addPointsTo(from: T, to: T) {
        if (!pointerStoreMembers.contains(from)) {
            addPointer(from)
        }
        if (!pointerStoreMembers.contains(to)) {
            addPointer(to)
        }
        this.pointsTo.add(from to to)
    }

    fun pointsTo(pointerStoreMember: T): Set<T> {
        if (!pointerStoreMembers.contains(pointerStoreMember)) {
            return emptySet()
        }
        return pointsTo.filter { it.first == pointerStoreMember }.map { it.second }.toSet()
    }

    fun has(pointerStoreMember: T): Boolean {
        return pointerStoreMembers.contains(pointerStoreMember)
    }

    fun toGraph() : Graph {
        val graph = Graph("\"" + UUID.randomUUID().toString() + "\"", "Pointer Analysis")
        val attrsBuilder = NodeAttributes.builder().shape(Shape.RECTANGLE)
                .fillColor(Color.WHITE).lineColor(Color.BLACK).alignment(Alignment.LEFT)
        pointerStoreMembers.forEach {
            graph.addNode("\"" + it + "\"", attrsBuilder.label(it.toString()).build())
        }
        val eAttrs = EdgeAttributes.builder().label("").color(Color.BLACK).lineStyle(LineStyle.NORMAL).font("courier").build()
        pointsTo.forEach { (source, target) -> run {
            graph.addEdge("\"" + source.toString() + "\"", "\"" + target.toString() + "\"", eAttrs)
        }}
        return graph
    }

    fun edgeCount() = pointsTo.size
}