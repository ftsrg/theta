package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.Event
import hu.bme.mit.theta.analysis.algorithm.oc.EventType
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

enum class OcDecisionProcedureType {
    BASIC, PROPAGATOR
}

/**
 * Important! Empty collection is converted to true (not false).
 */
internal fun Collection<Expr<BoolType>>.toAnd(): Expr<BoolType> = when (size) {
    0 -> BoolExprs.True()
    1 -> first()
    else -> BoolExprs.And(this)
}

internal class XcfaEvent(
    const: IndexedConstDecl<*>,
    type: EventType,
    guard: List<Expr<BoolType>>,
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
    val guard: Expr<BoolType>,
    val lastEvents: List<XcfaEvent>,
)

internal data class Thread(
    val procedure: XcfaProcedure,
    val guard: List<Expr<BoolType>> = listOf(),
    val pidVar: VarDecl<*>? = null,
    val startEvent: XcfaEvent? = null,
    val joinEvents: MutableSet<XcfaEvent> = mutableSetOf(),
    val pid: Int = uniqueId(),
) {

    companion object {

        private var cnt: Int = 0
        private fun uniqueId(): Int = cnt++
    }
}

internal data class SearchItem(val loc: XcfaLocation) {

    val guards: MutableList<List<Expr<BoolType>>> = mutableListOf()
    val lastEvents: MutableList<XcfaEvent> = mutableListOf()
    val lastWrites: MutableList<Map<VarDecl<*>, Set<XcfaEvent>>> = mutableListOf()
    val pidLookups: MutableList<Map<VarDecl<*>, Set<Pair<List<Expr<BoolType>>, Int>>>> = mutableListOf()
    val atomics: MutableList<Boolean?> = mutableListOf()
    var incoming: Int = 0
}

internal data class StackItem(val event: XcfaEvent) {

    var eventsToVisit: MutableList<XcfaEvent>? = null
}
