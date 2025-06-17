package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for not-equal (!=) expressions over equational types.
 */
@Serializable
abstract class NeqExpr<OpType : Equational<OpType>> : BinaryExpr<OpType, hu.bme.mit.theta.core.type.booltype.BoolType>() {

    companion object {
        @JvmStatic
        fun <OpType : Equational<OpType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): NeqExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as OpType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Neq(newLeftOp, newRightOp)
        }
    }
}

