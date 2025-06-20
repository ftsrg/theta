package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

/**
 * Abstract base class for greater-or-equal expressions over ordered types.
 */
@Serializable
abstract class GeqExpr<OpType : Ordered<OpType>> : BinaryExpr<OpType, BoolType>() {

    companion object {
        private const val OPERATOR_LABEL = ">="

        @JvmStatic
        fun <OpType : Ordered<OpType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): GeqExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as OpType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Geq(newLeftOp, newRightOp)
        }
    }

    override val type: BoolType = Bool()

    override val operatorLabel: String get() = OPERATOR_LABEL
}
