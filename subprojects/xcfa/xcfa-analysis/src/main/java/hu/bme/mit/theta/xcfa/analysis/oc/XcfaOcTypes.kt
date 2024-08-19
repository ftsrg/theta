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

package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

internal typealias E = XcfaEvent
internal typealias R = Relation<XcfaEvent>

@Suppress("unused")
enum class OcDecisionProcedureType(internal val checker: () -> OcChecker<E>) {

    BASIC({ BasicOcChecker() }),
    PROPAGATOR({ UserPropagatorOcChecker() }),
    PREVENTIVE({ PreventivePropagatorOcChecker() }),
}

/**
 * Important! Empty collection is converted to true (not false).
 */
internal fun Collection<Expr<BoolType>>.toAnd(): Expr<BoolType> = when (size) {
    0 -> BoolExprs.True()
    1 -> first()
    else -> And(this)
}

/**
 * Takes the OR of the contained lists mapped to an AND expression. Simplifications are made based on the list sizes.
 */
internal fun Collection<Set<Expr<BoolType>>>.toOrInSet(): Set<Expr<BoolType>> = when (size) {
    0 -> setOf()
    1 -> first()
    else -> setOf(Or(map { it.toAnd() }))
}

internal class XcfaEvent(
    const: IndexedConstDecl<*>,
    type: EventType,
    guard: Set<Expr<BoolType>>,
    pid: Int,
    val edge: XcfaEdge,
    clkId: Int = uniqueId()
) : Event(const, type, guard, pid, clkId) {

    companion object {

        private var cnt: Int = 0
        private fun uniqueId(): Int = cnt++
    }
}

internal data class Violation(
    val errorLoc: XcfaLocation,
    val pid: Int,
    val guard: Expr<BoolType>,
    val lastEvents: List<XcfaEvent>,
)

internal data class Thread(
    val procedure: XcfaProcedure,
    val guard: Set<Expr<BoolType>> = setOf(),
    val pidVar: VarDecl<*>? = null,
    val startEvent: XcfaEvent? = null,
    val startHistory: List<String> = listOf(),
    val lastWrites: Map<VarDecl<*>, Set<E>> = mapOf(),
    val pid: Int = uniqueId(),
) {

    val finalEvents: MutableSet<XcfaEvent> = mutableSetOf()

    companion object {

        private var cnt: Int = 0
        private fun uniqueId(): Int = cnt++
    }
}

internal data class SearchItem(val loc: XcfaLocation) {

    val guards: MutableList<Set<Expr<BoolType>>> = mutableListOf()
    val lastEvents: MutableList<XcfaEvent> = mutableListOf()
    val lastWrites: MutableList<Map<VarDecl<*>, Set<XcfaEvent>>> = mutableListOf()
    val threadLookups: MutableList<Map<VarDecl<*>, Set<Pair<Set<Expr<BoolType>>, Thread>>>> = mutableListOf()
    val atomics: MutableList<Boolean?> = mutableListOf()
    var incoming: Int = 0
}

internal data class StackItem(val event: XcfaEvent) {

    var eventsToVisit: MutableList<XcfaEvent>? = null
}
