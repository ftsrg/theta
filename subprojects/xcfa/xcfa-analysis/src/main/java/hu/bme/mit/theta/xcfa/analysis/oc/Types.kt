package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.decl.*
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure

internal object OcType : Type

internal object OcLitExpr : LitExpr<OcType>, NullaryExpr<OcType>() {

    override fun getType() = OcType
    override fun eval(`val`: Valuation?) = error("This expression is not meant to be evaluated.")
}

internal enum class EventType { WRITE, READ }
internal data class Event(
    val const: IndexedConstDecl<*>,
    val type: EventType,
    val guard: List<Expr<BoolType>>,
    val pid: Int,
    val edge: XcfaEdge,
    val id: Int = uniqueId()
) {

    var enabled: Boolean? = null

    companion object {

        private var cnt: Int = 0
        private fun uniqueId(): Int = cnt++
    }

    val clk: RefExpr<OcType> = RefExpr.of(Decls.Const("${const.name}\$clk_$pid", OcType))
    var assignment: Expr<BoolType>? = null

    fun enabled(valuation: Valuation): Boolean? {
        val e = try {
            And(guard).eval(valuation).value
        } catch (e: Exception) {
            null
        }
        enabled = e
        return e
    }

    override fun equals(other: Any?): Boolean {
        if (other !is Event) return false
        return id == other.id
    }

    override fun hashCode(): Int = id
}

internal enum class RelationType { PO, EPO, RFI, RFE }
internal data class Relation(
    val type: RelationType,
    val from: Event,
    val to: Event,
) : Expr<BoolType> {

    val decl: ConstDecl<BoolType> =
        Decls.Const("${type.toString().lowercase()}_${from.const.name}_${to.const.name}", Bool())
    val declRef: RefExpr<BoolType> = RefExpr.of(decl)
    var value: Boolean? = null

    override fun toString() = "Relation($type, ${from.const.name}[${from.type.toString()[0]}], ${to.const.name}[${to.type.toString()[0]}])"
    override fun getType(): BoolType = Bool()
    override fun getArity() = 2
    override fun getOps(): List<Expr<*>> = listOf(from.clk, to.clk)
    override fun eval(v: Valuation) = error("This expression is not meant to be evaluated.")
    override fun withOps(ops: List<Expr<*>>) = error("This expression is not meant to be modified.")
    fun enabled(valuation: Map<Decl<*>, LitExpr<*>>) = value(valuation) ?: false
    fun value(valuation: Map<Decl<*>, LitExpr<*>>): Boolean? {
        value = if (type == RelationType.PO || type == RelationType.EPO) true
        else valuation[decl]?.let { (it as BoolLitExpr).value }
        return value
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
    val incoming: MutableSet<XcfaEdge> = mutableSetOf()
}

internal data class StackItem(val event: Event) {

    var eventsToVisit: MutableList<Event>? = null
}