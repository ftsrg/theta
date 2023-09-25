package hu.bme.mit.theta.core.utils

import hu.bme.mit.theta.common.visualization.*
import hu.bme.mit.theta.core.decl.VarDecl
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

    fun pointsTo(pointerStoreMember: VarDecl<*>): Set<VarDecl<*>> {
        if (!pointerStoreMembers.contains(pointerStoreMember)) {
            return emptySet()
        }
        return pointsTo.filter { it.first == pointerStoreMember }.map { it.second }.toSet()
    }

    fun pointsTo_ByName_Unsafe(pointerStoreMember: VarDecl<*>): Set<VarDecl<*>> {
        return pointsTo.filter { it.first.name.contains(pointerStoreMember.name) }.map { it.second }.toSet()
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
}