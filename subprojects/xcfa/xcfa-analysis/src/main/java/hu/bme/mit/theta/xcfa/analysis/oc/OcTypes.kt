package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.decl.*
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

/**
 * Important! Empty collection is converted to true (not false).
 */
internal fun Collection<Expr<BoolType>>.toAnd(): Expr<BoolType> = when (size) {
    0 -> True()
    1 -> first()
    else -> And(this)
}

internal enum class EventType { WRITE, READ }
internal data class Event(
    val const: IndexedConstDecl<*>,
    val type: EventType,
    val guard: List<Expr<BoolType>>,
    val pid: Int,
    val edge: XcfaEdge,
    val clkId: Int = uniqueId()
) {

    val guardExpr: Expr<BoolType> = guard.toAnd()
    var assignment: Expr<BoolType>? = null
    var enabled: Boolean? = null

    companion object {

        private var cnt: Int = 0
        private fun uniqueId(): Int = cnt++
    }

    fun enabled(valuation: Valuation): Boolean? {
        val e = try {
            (guardExpr.eval(valuation) as? BoolLitExpr)?.value
        } catch (e: Exception) {
            null
        }
        enabled = e
        return e
    }
}

internal enum class RelationType { PO, EPO, RFI, RFE }
internal data class Relation(
    val type: RelationType,
    val from: Event,
    val to: Event,
) {

    val decl: ConstDecl<BoolType> =
        Decls.Const("${type.toString().lowercase()}_${from.const.name}_${to.const.name}", Bool())
    val declRef: RefExpr<BoolType> = RefExpr.of(decl)
    var enabled: Boolean? = null

    override fun toString() = "Relation($type, ${from.const.name}[${from.type.toString()[0]}], ${to.const.name}[${to.type.toString()[0]}])"
    fun enabled(valuation: Map<Decl<*>, LitExpr<*>>): Boolean? {
        enabled = if (type == RelationType.PO || type == RelationType.EPO) true
        else valuation[decl]?.let { (it as BoolLitExpr).value }
        return enabled
    }
}

internal data class Violation(
    val errorLoc: XcfaLocation,
    val guard: Expr<BoolType>,
    val lastEvents: List<Event>,
)

internal data class Thread(
    val procedure: XcfaProcedure,
    val guard: List<Expr<BoolType>> = listOf(),
    val pidVar: VarDecl<*>? = null,
    val startEvent: Event? = null,
    val joinEvents: MutableSet<Event> = mutableSetOf(),
    val pid: Int = uniqueId(),
) {

    companion object {

        private var cnt: Int = 0
        private fun uniqueId(): Int = cnt++
    }
}

internal data class SearchItem(val loc: XcfaLocation) {

    val guards: MutableList<List<Expr<BoolType>>> = mutableListOf()
    val lastEvents: MutableList<Event> = mutableListOf()
    val lastWrites: MutableList<Map<VarDecl<*>, Set<Event>>> = mutableListOf()
    val pidLookups: MutableList<Map<VarDecl<*>, Set<Pair<List<Expr<BoolType>>, Int>>>> = mutableListOf()
    val atomics: MutableList<Boolean?> = mutableListOf()
    var incoming: Int = 0
}

internal data class StackItem(val event: Event) {

    var eventsToVisit: MutableList<Event>? = null
}
