package hu.bme.mit.theta.core.type.enumtype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("EnumEqExpr")
data class EnumEqExpr(
    override val leftOp: Expr<EnumType>,
    override val rightOp: Expr<EnumType>
) : EqExpr<EnumType>() {

    companion object {

        private const val OPERATOR_LABEL = "="
        @JvmStatic
        fun of(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>) = EnumEqExpr(leftOp, rightOp)
    }

    override val operatorLabel: String = OPERATOR_LABEL
    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): LitExpr<BoolType> =
        EnumLitExpr.eq(leftOp.eval(`val`) as EnumLitExpr, rightOp.eval(`val`) as EnumLitExpr)

    override fun of(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): EnumEqExpr =
        Companion.of(leftOp, rightOp)

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL)
        .body()
        .add(leftOp)
        .add(rightOp)
        .toString()
}
