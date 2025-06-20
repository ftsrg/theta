package hu.bme.mit.theta.core.type.booltype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * Logical XOR expression for boolean type.
 */
@Serializable
@SerialName("Xor")
data class XorExpr(
    override val leftOp: Expr<BoolType>,
    override val rightOp: Expr<BoolType>
) : NeqExpr<BoolType>() {

    companion object {

        private const val OPERATOR_LABEL = "xor"
        @JvmStatic
        fun of(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>) = XorExpr(leftOp, rightOp)
        @JvmStatic
        fun create(leftOp: Expr<*>, rightOp: Expr<*>) = XorExpr(cast(leftOp, Bool()), cast(rightOp, Bool()))
    }

    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): BoolLitExpr =
        Bool((leftOp.eval(`val`) as BoolLitExpr).value != (rightOp.eval(`val`) as BoolLitExpr).value)

    override fun of(leftOp: Expr<BoolType>, rightOp: Expr<BoolType>): XorExpr =
        Companion.of(leftOp, rightOp)

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL).add(leftOp).add(rightOp).toString()
    override val operatorLabel: String get() = OPERATOR_LABEL
}
