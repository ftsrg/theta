package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for subtraction expressions over additive types.
 */
@Serializable
abstract class SubExpr<ExprType : Additive<ExprType>> : BinaryExpr<ExprType, ExprType>() {

    companion object {
        @JvmStatic
        fun <ExprType : Additive<ExprType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): SubExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as ExprType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Sub(newLeftOp, newRightOp)
        }
    }
}
