package hu.bme.mit.theta.core.type.enumtype

import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("EnumNeqExpr")
data class EnumNeqExpr(
    override val leftOp: Expr<EnumType>,
    override val rightOp: Expr<EnumType>
) : NeqExpr<EnumType>() {

    companion object {

        private const val OPERATOR_LABEL = "!="
        @JvmStatic
        fun of(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>) = EnumNeqExpr(leftOp, rightOp)
    }

    override val operatorLabel: String = OPERATOR_LABEL
    override val type: BoolType = Bool()
    override fun eval(`val`: Valuation): LitExpr<BoolType> =
        EnumLitExpr.neq(leftOp.eval(`val`) as EnumLitExpr, rightOp.eval(`val`) as EnumLitExpr)

    override fun of(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): EnumNeqExpr =
        Companion.of(leftOp, rightOp)

    override fun toString(): String = Utils.lispStringBuilder(OPERATOR_LABEL)
        .body()
        .add(leftOp)
        .add(rightOp)
        .toString()
}
