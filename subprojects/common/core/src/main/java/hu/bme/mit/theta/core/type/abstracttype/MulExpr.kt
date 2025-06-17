package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for multiplication expressions over types that support multiplication.
 */
@Serializable
abstract class MulExpr<ExprType : Multiplicative<ExprType>> : MultiaryExpr<ExprType, ExprType>() {

    companion object {
        @JvmStatic
        fun <ExprType : Multiplicative<ExprType>> create2(
            ops: List<Expr<*>>
        ): MulExpr<*> {
            require(ops.isNotEmpty())
            @Suppress("UNCHECKED_CAST")
            val type = ops[0].type as ExprType
            return type.Mul(ops.map { cast(it, type) })
        }
    }
}

