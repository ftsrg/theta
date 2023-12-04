/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.utils

import hu.bme.mit.theta.common.visualization.*
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import java.awt.Color
import java.util.*
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.anytype.DeRefExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs

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

    fun toGraph(): Graph {
        val graph = Graph("\"" + UUID.randomUUID().toString() + "\"", "Pointer Analysis")
        val attrsBuilder = NodeAttributes.builder().shape(Shape.RECTANGLE)
            .fillColor(Color.WHITE).lineColor(Color.BLACK).alignment(Alignment.LEFT)
        pointerStoreMembers.forEach {
            graph.addNode("\"" + it + "\"", attrsBuilder.label(it.toString()).build())
        }
        val eAttrs = EdgeAttributes.builder().label("").color(Color.BLACK).lineStyle(LineStyle.NORMAL).font("courier")
            .build()
        pointsTo.forEach { (source, target) ->
            run {
                graph.addEdge("\"" + source.toString() + "\"", "\"" + target.toString() + "\"", eAttrs)
            }
        }
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

    fun nodes() = pointerStoreMembers

    fun toExpr(): Expr<BoolType> {
        val ops = mutableSetOf<NeqExpr<*>>()
        pointerStoreMembers.forEach { v1 ->
            pointerStoreMembers.forEach { v2 ->
                val v1PointsTo = pointsTo(v1)
                val v2PointsTo = pointsTo(v2)
                if (v1PointsTo.size == 1 && v2PointsTo.size == 1 && v1PointsTo != v2PointsTo && !ops.contains(
                        Neq(v2.ref, v1.ref))) {
                    ops.add(Neq(v1.ref, v2.ref))
                }
            }
        }
        return SmartBoolExprs.And(ops)
    }

    fun deRefLut(): Map<DeRefExpr<*>, VarDecl<*>> {
        val deRefLut = pointsTo.map { (source, target) -> DeRefExpr.of(RefExpr.of(source)) to target }.toMap()
        return deRefLut
    }
}