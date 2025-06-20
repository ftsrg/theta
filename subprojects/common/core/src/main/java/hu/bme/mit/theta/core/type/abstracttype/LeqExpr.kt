package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for less-or-equal (≤) expressions over ordered types.
 */
@Serializable
abstract class LeqExpr<OpType : Ordered<OpType>> : BinaryExpr<OpType, BoolType>() {

    companion object {
        @JvmStatic
        fun <OpType : Ordered<OpType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): LeqExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as OpType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Leq(newLeftOp, newRightOp)
        }
    }
}
