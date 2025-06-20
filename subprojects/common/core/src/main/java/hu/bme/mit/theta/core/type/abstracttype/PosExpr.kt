package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.UnaryExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for positive (unary plus) expressions over additive types.
 */
@Serializable
abstract class PosExpr<ExprType : Additive<ExprType>> : UnaryExpr<ExprType, ExprType>() {

    companion object {
        @JvmStatic
        fun <ExprType : Additive<ExprType>> create2(
            op: Expr<*>
        ): PosExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = op.type as ExprType
            val newOp = cast(op, type)
            return type.Pos(newOp)
        }
    }
}
