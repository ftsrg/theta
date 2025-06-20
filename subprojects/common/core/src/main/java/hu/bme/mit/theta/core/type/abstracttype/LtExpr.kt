package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for less-than (<) expressions over ordered types.
 */
@Serializable
abstract class LtExpr<OpType : Ordered<OpType>> : BinaryExpr<OpType, BoolType>() {

    companion object {
        @JvmStatic
        fun <OpType : Ordered<OpType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): LtExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as OpType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Lt(newLeftOp, newRightOp)
        }
    }
}
