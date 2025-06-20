package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Logical NOT expression for boolean type.
 */
@Serializable
@SerialName("Not")
data class NotExpr(
    override val op: Expr<BoolType>
) : UnaryExpr<BoolType, BoolType>() {

    companion object {

        private const val OPERATOR_LABEL = "not"

        @JvmStatic
        fun of(op: Expr<BoolType>) = NotExpr(op)
        @JvmStatic
        fun create(op: Expr<*>) = NotExpr(cast(op, Bool()))
    }

    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): BoolLitExpr = Bool(!(op.eval(`val`) as BoolLitExpr).value)
    override fun of(op: Expr<BoolType>): NotExpr = NotExpr(op)
    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL).add(op).toString()
    override val operatorLabel: String = OPERATOR_LABEL
}
