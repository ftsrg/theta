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
 * Logical OR expression for boolean type.
 */
@Serializable
@SerialName(OrExpr.OPERATOR_LABEL)
data class OrExpr(
    override val ops: List<Expr<BoolType>>
) : MultiaryExpr<BoolType, BoolType>() {

    companion object {

        internal const val OPERATOR_LABEL = "or"
        fun of(ops: Iterable<Expr<BoolType>>) = OrExpr(ops.toList())
        fun create(ops: List<Expr<*>>) = OrExpr(ops.map { cast(it, Bool()) })
    }

    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): BoolLitExpr =
        if (ops.any { (it.eval(`val`) as BoolLitExpr).value }) True() else False()

    override fun with(ops: Iterable<Expr<BoolType>>): OrExpr =
        if (ops.toList() == this.ops) this else OrExpr(ops.toList())

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL).add(ops).toString()
    override val operatorLabel: String get() = OPERATOR_LABEL
}

