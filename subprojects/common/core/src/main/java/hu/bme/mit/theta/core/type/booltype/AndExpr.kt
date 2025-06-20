package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Logical AND expression for boolean type.
 */
@Serializable
@SerialName(AndExpr.OPERATOR_LABEL)
data class AndExpr(
    override val ops: List<Expr<BoolType>>
) : MultiaryExpr<BoolType, BoolType>() {

    companion object {

        internal const val OPERATOR_LABEL = "and"
        fun of(ops: Iterable<Expr<BoolType>>) = AndExpr(ops.toList())
        fun create(ops: List<Expr<*>>) = AndExpr(ops.map { cast(it, Bool()) })
    }

    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): BoolLitExpr =
        if (ops.any { !(it.eval(`val`) as BoolLitExpr).value }) False() else True()

    override fun with(ops: Iterable<Expr<BoolType>>): AndExpr =
        if (ops.toList() == this.ops) this else AndExpr(ops.toList())

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL).add(ops).toString()
    override val operatorLabel: String get() = OPERATOR_LABEL
}

