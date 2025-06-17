package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for modulo (mod) expressions over divisible types.
 */
@Serializable
abstract class ModExpr<ExprType : Divisible<ExprType>> : BinaryExpr<ExprType, ExprType>() {

    companion object {
        @JvmStatic
        fun <ExprType : Divisible<ExprType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): ModExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as ExprType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Mod(newLeftOp, newRightOp)
        }
    }
}

