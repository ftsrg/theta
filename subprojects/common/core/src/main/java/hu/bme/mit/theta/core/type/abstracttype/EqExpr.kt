package hu.bme.mit.theta.core.type.abstracttype

import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import kotlinx.serialization.Serializable

@Serializable
abstract class EqExpr<OpType : Equational<OpType>> : BinaryExpr<OpType, BoolType>() {

    companion object {

        @JvmStatic
        fun <OpType : Equational<OpType>> create2(
            leftOp: Expr<*>,
            rightOp: Expr<*>
        ): EqExpr<*> {
            @Suppress("UNCHECKED_CAST")
            val type = leftOp.type as OpType
            val newLeftOp = cast(leftOp, type)
            val newRightOp = cast(rightOp, type)
            return type.Eq(newLeftOp, newRightOp)
        }
    }
}

