package hu.bme.mit.theta.core.utils

import hu.bme.mit.theta.common.visualization.*
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.anytype.DeRefExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import java.awt.Color
import java.util.*

class PointerStore {
    private val pointerStoreMembers: MutableSet<VarDecl<*>> = mutableSetOf()
    private val pointsTo: MutableSet<Pair<VarDecl<*>, VarDecl<*>>> = mutableSetOf()

    fun clear() {
        pointerStoreMembers.clear()
        pointsTo.clear()
    }

    fun addPointer(pointerStoreMember: VarDecl<*>) {
        pointerStoreMembers.add(pointerStoreMember)
    }

    fun addPointsTo(from: VarDecl<*>, to: VarDecl<*>) {
        if (!pointerStoreMembers.contains(from)) {
            addPointer(from)
        }
        if (!pointerStoreMembers.contains(to)) {
            addPointer(to)
        }
        this.pointsTo.add(from to to)
    }

    fun removePointsToAny(from: VarDecl<*>) {
        pointsTo.removeIf { it.first == from }
    }

    fun pointsTo(pointerStoreMember: VarDecl<*>): Set<VarDecl<*>> {
        if (!pointerStoreMembers.contains(pointerStoreMember)) {
            return emptySet()
        }
        return pointsTo.filter { it.first == pointerStoreMember }.map { it.second }.toSet()
    }
    
    fun has(pointerStoreMember: VarDecl<*>): Boolean {
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

    override fun toString(): String {
        return pointsTo.joinToString(",") { (source, target) -> "$source -> $target" }
    }

    fun edgeCount() = pointsTo.size
    fun copy(): PointerStore {
        val copy = PointerStore()
        copy.pointerStoreMembers.addAll(pointerStoreMembers)
        copy.pointsTo.addAll(pointsTo)
        return copy
    }

    fun isLeq(other: PointerStore): Boolean {
        return pointsTo.all { (source, target) -> other.pointsTo(source).contains(target) }
    }
}