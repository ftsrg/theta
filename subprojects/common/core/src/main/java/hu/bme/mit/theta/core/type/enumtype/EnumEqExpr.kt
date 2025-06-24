package hu.bme.mit.theta.core.type.enumtype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
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

        @JvmStatic
        fun of(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>) = EnumEqExpr(leftOp, rightOp)
    }

    override fun eval(`val`: Valuation): LitExpr<BoolType> =
        EnumLitExpr.eq(leftOp.eval(`val`) as EnumLitExpr, rightOp.eval(`val`) as EnumLitExpr)

    override fun new(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): EnumEqExpr =
        of(leftOp, rightOp)

    override fun toString(): String = super.toString()
}
