/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.oc


import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus

internal inline fun <reified T> Array<Array<T?>>.copy(): Array<Array<T?>> =
    Array(size) { i -> Array(size) { j -> this[i][j] } }

interface OcChecker<E : Event> {

    val solver: Solver

    fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>,
        pos: List<Relation<E>>,
        rfs: Map<VarDecl<*>, List<Relation<E>>>
    ): SolverStatus?

    fun getRelations(): Array<Array<Reason?>>?
}

internal interface OcCheckerBase<E : Event> : OcChecker<E> {

    fun derive(rels: Array<Array<Reason?>>, rf: Relation<E>, w: E): Reason? = when {
        rf.from.clkId == rf.to.clkId -> null // rf within an atomic block
        w.clkId == rf.from.clkId || w.clkId == rf.to.clkId -> null // w within an atomic block with one of the rf ends

        rels[w.clkId][rf.to.clkId] != null -> { // WS derivation
            val reason = WriteSerializationReason(rf, w, rels[w.clkId][rf.to.clkId]!!)
            setAndClose(rels, w.clkId, rf.from.clkId, reason)
        }

        rels[rf.from.clkId][w.clkId] != null -> { // FR derivation
            val reason = FromReadReason(rf, w, rels[rf.from.clkId][w.clkId]!!)
            setAndClose(rels, rf.to.clkId, w.clkId, reason)
        }

        else -> null
    }

    fun setAndClose(rels: Array<Array<Reason?>>, rel: Relation<E>): Reason? {
        if (rel.from.clkId == rel.to.clkId) return null // within an atomic block
        return setAndClose(rels, rel.from.clkId, rel.to.clkId,
            if (rel.type == RelationType.PO) PoReason else RelationReason(rel))
    }

    private fun setAndClose(rels: Array<Array<Reason?>>, from: Int, to: Int, reason: Reason): Reason? {
        if (from == to) return reason // cycle (self-loop) found
        val toClose = mutableListOf(from to to to reason)
        while (toClose.isNotEmpty()) {
            val (fromTo, r) = toClose.removeFirst()
            val (i1, i2) = fromTo
            check(i1 != i2)
            if (rels[i1][i2] != null) continue

            rels[i1][i2] = r
            rels[i2].forEachIndexed { i2next, b ->
                if (b != null && rels[i1][i2next] == null) { // i2 -> i2next, not i1 -> i2next
                    val combinedReason = r and b
                    if (i1 == i2next) return combinedReason // cycle (self-loop) found
                    toClose.add(i1 to i2next to combinedReason)
                }
            }
            rels.forEachIndexed { i1previous, b ->
                if (b[i1] != null && rels[i1previous][i2] == null) { // i1previous -> i1, not i1previous -> i2
                    val combinedReason = r and b[i1]!!
                    if (i1previous == i2) return combinedReason // cycle (self-loop) found
                    toClose.add(i1previous to i2 to combinedReason)
                }
            }
        }
        return null
    }
}


sealed class Reason {

    open val reasons: List<Reason> get() = listOf(this)
    val exprs: List<Expr<BoolType>> get() = toExprs()
    val expr: Expr<BoolType> get() = exprs.toAnd()
    infix fun and(other: Reason): Reason = CombinedReason(reasons + other.reasons)
    open fun toExprs(): List<Expr<BoolType>> = reasons.map { it.toExprs() }.flatten().filter { it !is TrueExpr }
}

class CombinedReason(override val reasons: List<Reason>) : Reason()
object PoReason : Reason() {

    override val reasons get() = emptyList<Reason>()
    override fun toExprs(): List<Expr<BoolType>> = listOf()
}

class RelationReason<E : Event>(val relation: Relation<E>) : Reason() {

    override fun toExprs(): List<Expr<BoolType>> = listOf(relation.declRef)
}

sealed class DerivedReason<E : Event>(val rf: Relation<E>, val w: Event, val wRfRelation: Reason) : Reason() {

    override fun toExprs(): List<Expr<BoolType>> = listOf(rf.declRef, w.guardExpr) + wRfRelation.toExprs()
}

class WriteSerializationReason<E : Event>(rf: Relation<E>, w: Event, wBeforeRf: Reason) :
    DerivedReason<E>(rf, w, wBeforeRf)

class FromReadReason<E : Event>(rf: Relation<E>, w: Event, wAfterRf: Reason) :
    DerivedReason<E>(rf, w, wAfterRf)

internal class OcAssignment<E : Event>(
    val relation: Relation<E>? = null,
    val event: E? = null,
    val rels: Array<Array<Reason?>>,
    val solverLevel: Int = 0,
) {

    constructor(rels: Array<Array<Reason?>>, e: E, solverLevel: Int = 0)
        : this(event = e, rels = rels.copy(), solverLevel = solverLevel)

    constructor(rels: Array<Array<Reason?>>, r: Relation<E>, solverLevel: Int = 0)
        : this(relation = r, rels = rels.copy(), solverLevel = solverLevel)

    override fun toString(): String {
        return "OcAssignment(relation=$relation, event=$event, solverLevel=$solverLevel)"
    }
}
