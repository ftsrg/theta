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

import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType

/**
 * Important! Empty collection is converted to true (not false).
 */
internal fun Collection<Expr<BoolType>>.toAnd(): Expr<BoolType> = when (size) {
    0 -> BoolExprs.True()
    1 -> first()
    else -> BoolExprs.And(this)
}

enum class EventType { WRITE, READ }
abstract class Event(
    val const: IndexedConstDecl<*>,
    val type: EventType,
    val guard: List<Expr<BoolType>>,
    val pid: Int,
    val clkId: Int
) {

    val guardExpr: Expr<BoolType> = guard.toAnd()
    var assignment: Expr<BoolType>? = null
    var enabled: Boolean? = null

    fun enabled(valuation: Valuation): Boolean? {
        val e = try {
            (guardExpr.eval(valuation) as? BoolLitExpr)?.value
        } catch (e: Exception) {
            null
        }
        enabled = e
        return e
    }

    override fun toString(): String {
        return "Event(pid=$pid, clkId=$clkId, ${const.name}[${type.toString()[0]}], guard=$guard)"
    }
}

enum class RelationType { PO, RFI, RFE }
data class Relation<E : Event>(
    val type: RelationType,
    val from: E,
    val to: E,
) {

    val decl: ConstDecl<BoolType> =
        Decls.Const("${type.toString().lowercase()}_${from.const.name}_${to.const.name}", BoolExprs.Bool())
    val declRef: RefExpr<BoolType> = RefExpr.of(decl)
    var enabled: Boolean? = null

    override fun toString() = "Relation($type, ${from.const.name}[${from.type.toString()[0]}], ${to.const.name}[${to.type.toString()[0]}])"
    fun enabled(valuation: Map<Decl<*>, LitExpr<*>>): Boolean? {
        enabled = if (type == RelationType.PO) true else valuation[decl]?.let { (it as BoolLitExpr).value }
        return enabled
    }
}