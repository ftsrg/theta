package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for division expressions over types that support multiplication and division.
 * Used to represent division operations in the expression tree.
 */
@Serializable
abstract class DivExpr<ExprType : Multiplicative<ExprType>> : BinaryExpr<ExprType, ExprType>() {

    companion object {

        @JvmStatic
        fun <ExprType : Multiplicative<ExprType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): DivExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as ExprType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Div(newLeftOp, newRightOp)
        }
    }
}
