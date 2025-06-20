package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Logical implication (=>) expression for boolean type.
 */
@Serializable
@SerialName("Imply")
data class ImplyExpr(
    override val leftOp: Expr<BoolType>,
    override val rightOp: Expr<BoolType>
) : BinaryExpr<BoolType, BoolType>() {
    companion object {
        internal const val OPERATOR_LABEL = "=>"
        fun of(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = ImplyExpr(leftOp, rightOp)
        fun create(leftOp: Expr<*>, rightOp: Expr<*>) = ImplyExpr(cast(leftOp, Bool()), cast(rightOp, Bool()))
    }
    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): BoolLitExpr =
        Bool(!(leftOp.eval(`val`) as BoolLitExpr).value || (rightOp.eval(`val`) as BoolLitExpr).value)
    override fun of(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): ImplyExpr =
        ImplyExpr(leftOp, rightOp)
    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL).add(leftOp).add(rightOp).toString()
    override val operatorLabel: String get() = OPERATOR_LABEL
}

