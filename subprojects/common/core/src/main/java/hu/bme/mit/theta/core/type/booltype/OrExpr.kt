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
@SerialName("Or")
data class OrExpr(
    override val ops: List<Expr<BoolType>>
) : MultiaryExpr<BoolType, BoolType>() {

    companion object {

        private const val OPERATOR_LABEL = "or"

        @JvmStatic
        fun of(ops: Iterable<Expr<BoolType>>) = OrExpr(ops.toList())

        @JvmStatic
        fun create(ops: List<Expr<*>>) = OrExpr(ops.map { cast(it, Bool()) })
    }

    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): BoolLitExpr =
        if (ops.any { (it.eval(`val`) as BoolLitExpr).value }) True() else False()

    override fun of(ops: List<Expr<BoolType>>): OrExpr =
        Companion.of(ops)

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL).add(ops).toString()
    override val operatorLabel: String get() = OPERATOR_LABEL
}
