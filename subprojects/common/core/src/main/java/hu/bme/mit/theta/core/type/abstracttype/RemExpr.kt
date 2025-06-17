package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for remainder expressions over divisible types.
 */
@Serializable
abstract class RemExpr<ExprType : Divisible<ExprType>> : BinaryExpr<ExprType, ExprType>() {

    companion object {
        @JvmStatic
        fun <ExprType : Divisible<ExprType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): RemExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as ExprType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Rem(newLeftOp, newRightOp)
        }
    }
}

